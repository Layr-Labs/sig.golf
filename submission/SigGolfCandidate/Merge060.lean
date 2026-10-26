import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge042
import SigGolfCandidate.Merge044
import SigGolfCandidate.Merge046
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge049
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge056
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059

-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePass ====
section

/-! # T51 expand decoder DEC (words 54569 .. 54738): the machine blocks

Entered from word 0 (`j 54569`). D1 (54569..54646) collects the 29-bit field `X` from the top `b_j` bits of the path
nodes of heights `j = 3..10` (compact digests 168..175, high dwords at `aH j`), clears those bits, stores the hint
`X >> 16` at `0x66000` and branches on `hint < 7744` (else `j 354`). D3 (54648..54665) reads the 11-byte tail
(compact slot 324) into `s3`/`s4` (with `X % 2^16` at bit 88 of the sibling) and sets up the first move loop.
L1..L5 move the compact slots `[c0, c0 + n]` up by `o` slots, top-down (176..323 by 8, 88..175 by 4, 63..87 by 3,
38..62 by 2, 13..37 by 1). D6 (54712..54738) zeroes the 7 unused slots 13/39/65/91/181/182/183, writes the
sibling at slot 180, zeroes the temporaries and jumps to word 1. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- Absolute dword address of slot `k`, word `w` (`w = 0` low, `1` high) of the decode buffer at `0x7000`. -/
def slotA (k w : Nat) : Word := BitVec.ofNat 64 (0x7000 + 16 * k + 8 * w)

/-- Memory after D1, as a function of the memory `M` before it. -/
def d1Mem (M : Word → Word) (A : Word) : Word :=
  if A = BitVec.ofNat 64 417792 then xD M >>> 16
  else if A = aH 10 then clr 7 (M (aH 10))
  else if A = aH 9 then clr 6 (M (aH 9))
  else if A = aH 8 then clr 5 (M (aH 8))
  else if A = aH 7 then clr 4 (M (aH 7))
  else if A = aH 6 then clr 3 (M (aH 6))
  else if A = aH 5 then clr 2 (M (aH 5))
  else if A = aH 4 then clr 1 (M (aH 4))
  else if A = aH 3 then clr 1 (M (aH 3))
  else M A

/-! ## D1 -/
def codeD1 : List (BitVec 32) := (t51Code.drop 393).take 78
theorem codeAt_D1 : CodeAt Images.expandImage (pcOf 54569) codeD1 :=
  codeAt_t51_at 54569 (by decide) (by decide) (by decide)
sym_block eD1 := symRun { noAlias := true } codeD1 (pcOf 54569) 100

theorem eD1_mem (s : MachineState) (A : Word) : memEval s eD1.res.st.mem A = d1Mem s.getMem A := rfl
theorem eD1_x18 (s : MachineState) : (eD1.res.st.regs.get .x18).eval s = xD s.getMem := rfl
theorem eD1_pc (s : MachineState) : eD1.res.pc.eval s =
    if BitVec.ult (xD s.getMem >>> 16) 7744#64 then pcOf 54648 else pcOf 54647 := rfl

theorem d1_spec (s : MachineState) (hpc : s.pc = pcOf 54569) :
    ∃ t, Steps Images.expandImage s 78 78 t ∧
      t.pc = (if (xD s.getMem >>> 16).toNat < 7744 then pcOf 54648 else pcOf 54647) ∧
      t.getReg .x18 = xD s.getMem ∧ RegsExcept s t [.x6, .x7, .x18, .x28] ∧
      ∀ A, t.getMem A = d1Mem s.getMem A := by
  refine ⟨_, symRun_sound eD1 codeAt_D1 s hpc trivial, ?_, ?_, ?_, fun A => eD1_mem s A⟩
  · rw [Result.toState_pc, eD1_pc]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    by_cases h : (xD s.getMem >>> 16).toNat < 7744
    · rw [if_pos (by simpa using h), if_pos h]
    · rw [if_neg (by simpa using h), if_neg h]
  · rw [Result.toState_getReg]; exact eD1_x18 s
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl

/-! ## D3 (tail, sibling high word, L1 setup) -/
def codeD3 : List (BitVec 32) := (t51Code.drop 472).take 18
theorem codeAt_D3 : CodeAt Images.expandImage (pcOf 54648) codeD3 :=
  codeAt_t51_at 54648 (by decide) (by decide) (by decide)
sym_block eD3 := symRun { noAlias := true } codeD3 (pcOf 54648) 100

theorem d3_spec (s : MachineState) (hpc : s.pc = pcOf 54648) :
    ∃ t, Steps Images.expandImage s 18 18 t ∧ t.pc = pcOf 54666 ∧
      t.getReg .x19 = s.getMem (BitVec.ofNat 64 0x8440) ∧
      t.getReg .x20 = sibHi (s.getMem (BitVec.ofNat 64 0x8448)) (s.getReg .x18) ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * (176 + 147)) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 176) ∧
      RegsExcept s t [.x7, .x19, .x20, .x28, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eD3 codeAt_D3 s hpc trivial, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _
    rfl

/-! ## The move loops -/
theorem ofNat_sub16 (A : Nat) (hA : 16 ≤ A) (hA' : A < 2 ^ 64) :
    (BitVec.ofNat 64 A + 18446744073709551600#64 : Word) = BitVec.ofNat 64 (A - 16) := by
  rw [show (18446744073709551600#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 16) from rfl, ofNat_add_ofNat,
    show A + (2 ^ 64 - 16) = (A - 16) + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]

/-- One iteration of a DEC move loop at `head`: copy the 16 bytes at `t3` to `t3 + D`, `t3 -= 16`,
`bge t3,t5,head`. -/
def StepOK (im : Image) (head D : Nat) : Prop :=
  ∀ (s : MachineState) (A lo : Nat), s.pc = pcOf head → s.getReg .x28 = BitVec.ofNat 64 A →
    s.getReg .x30 = BitVec.ofNat 64 lo → 16 ≤ A → A + D + 16 ≤ 2 ^ 24 → lo < 2 ^ 24 → A % 8 = 0 →
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if lo + 16 ≤ A then pcOf head else pcOf (head + 6)) ∧
      t.getReg .x28 = BitVec.ofNat 64 (A - 16) ∧ t.getReg .x30 = BitVec.ofNat 64 lo ∧
      t.getMem (BitVec.ofNat 64 (A + D)) = s.getMem (BitVec.ofNat 64 A) ∧
      t.getMem (BitVec.ofNat 64 (A + D + 8)) = s.getMem (BitVec.ofNat 64 (A + 8)) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun X => X = A + D ∨ X = A + D + 8)

def codeL1 : List (BitVec 32) := (t51Code.drop 490).take 6
theorem codeAt_L1 : CodeAt Images.expandImage (pcOf 54666) codeL1 :=
  codeAt_t51_at 54666 (by decide) (by decide) (by decide)
sym_block eL1 := symRun { noAlias := true } codeL1 (pcOf 54666) 30

theorem stepL1 : StepOK Images.expandImage 54666 128 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL1 codeAt_L1 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL1.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL1.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL1.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

def codeL2 : List (BitVec 32) := (t51Code.drop 500).take 6
theorem codeAt_L2 : CodeAt Images.expandImage (pcOf 54676) codeL2 :=
  codeAt_t51_at 54676 (by decide) (by decide) (by decide)
sym_block eL2 := symRun { noAlias := true } codeL2 (pcOf 54676) 30

theorem stepL2 : StepOK Images.expandImage 54676 64 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL2 codeAt_L2 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL2.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL2.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL2.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

def codeL3 : List (BitVec 32) := (t51Code.drop 510).take 6
theorem codeAt_L3 : CodeAt Images.expandImage (pcOf 54686) codeL3 :=
  codeAt_t51_at 54686 (by decide) (by decide) (by decide)
sym_block eL3 := symRun { noAlias := true } codeL3 (pcOf 54686) 30

theorem stepL3 : StepOK Images.expandImage 54686 48 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL3 codeAt_L3 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL3.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL3.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL3.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

def codeL4 : List (BitVec 32) := (t51Code.drop 520).take 6
theorem codeAt_L4 : CodeAt Images.expandImage (pcOf 54696) codeL4 :=
  codeAt_t51_at 54696 (by decide) (by decide) (by decide)
sym_block eL4 := symRun { noAlias := true } codeL4 (pcOf 54696) 30

theorem stepL4 : StepOK Images.expandImage 54696 32 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL4 codeAt_L4 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL4.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL4.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL4.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

def codeL5 : List (BitVec 32) := (t51Code.drop 530).take 6
theorem codeAt_L5 : CodeAt Images.expandImage (pcOf 54706) codeL5 :=
  codeAt_t51_at 54706 (by decide) (by decide) (by decide)
sym_block eL5 := symRun { noAlias := true } codeL5 (pcOf 54706) 30

theorem stepL5 : StepOK Images.expandImage 54706 16 := by
  intro s A lo hpc h28 h30 hA hb hlo h8
  refine ⟨_, symRun_sound eL5 codeAt_L5 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eL5.res, rv_simp, h28, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, eL5.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30]
    rw [ofNat_sub16 A hA (by omega), ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : lo + 16 ≤ A
    · rw [if_pos h, decide_eq_false (by omega)]; rfl
    · rw [if_neg h, decide_eq_true (by omega)]; rfl
  · rw [Result.toState_getReg]
    change s.getReg .x28 + (18446744073709551600#64 : Word) = _
    rw [h28, ofNat_sub16 A hA (by omega)]
  · rw [Result.toState_getReg]; exact h30
  · simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
    rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro X hX hn
    simp only [Result.toState_getMem, eL5.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

/-- `n + 1` iterations, from `t3 = lo + 16 n` down to `lo`: the block `[lo, lo + 16 (n + 1))` moves up by `D`. -/
theorem move_loop {im : Image} {head D : Nat} (hstep : StepOK im head D) (hD : 16 ≤ D) :
    ∀ n (s : MachineState) (lo : Nat), 16 ≤ lo → lo % 8 = 0 → lo + 16 * (n + 1) + D ≤ 2 ^ 24 →
      s.pc = pcOf head → s.getReg .x28 = BitVec.ofNat 64 (lo + 16 * n) → s.getReg .x30 = BitVec.ofNat 64 lo →
      ∃ t, Steps im s (6 * (n + 1)) (6 * (n + 1)) t ∧ t.pc = pcOf (head + 6) ∧
        (∀ j, j ≤ n → t.getMem (BitVec.ofNat 64 (lo + 16 * j + D)) = s.getMem (BitVec.ofNat 64 (lo + 16 * j)) ∧
          t.getMem (BitVec.ofNat 64 (lo + 16 * j + D + 8)) = s.getMem (BitVec.ofNat 64 (lo + 16 * j + 8))) ∧
        RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun X => lo + D ≤ X ∧ X < lo + 16 * (n + 1) + D) := by
  intro n
  induction n with
  | zero =>
    intro s lo hlo hlo8 hb hpc h28 h30
    obtain ⟨t, st, pt, t28, t30, m0, m8, rt, ft⟩ := hstep s (lo + 16 * 0) lo hpc h28 h30 (by omega) (by omega)
      (by omega) (by omega)
    refine ⟨t, st, by rw [pt, if_neg (by omega)], ?_, rt, ft.mono (fun X _ h => by omega)⟩
    intro j hj
    obtain rfl : j = 0 := by omega
    exact ⟨m0, m8⟩
  | succ n ih =>
    intro s lo hlo hlo8 hb hpc h28 h30
    obtain ⟨u, su, pu, u28, u30, m0, m8, ru, fu⟩ := hstep s (lo + 16 * (n + 1)) lo hpc h28 h30 (by omega)
      (by omega) (by omega) (by omega)
    rw [if_pos (by omega)] at pu
    obtain ⟨t, ut, pt, mt, rt, ft⟩ := ih u lo hlo hlo8 (by omega) pu
      (by rw [u28, show lo + 16 * (n + 1) - 16 = lo + 16 * n by omega]) u30
    refine ⟨t, (su.trans ut).of_eq (by omega) (by omega), pt, ?_, (ru.trans rt).mono (by decide),
      (fu.trans ft).mono (fun X _ h => by rcases h with (h | h) | h <;> omega)⟩
    intro j hj
    by_cases hjn : j = n + 1
    · subst hjn
      refine ⟨?_, ?_⟩
      · rw [ft.get (by omega) (by omega), m0]
      · rw [ft.get (by omega) (by omega), m8]
    · obtain ⟨a, b⟩ := mt j (by omega)
      refine ⟨a.trans ?_, b.trans ?_⟩
      · exact fu.get (by omega) (by omega)
      · exact fu.get (by omega) (by omega)

/-- The source slot of slot `k` for a move of the slots `[c0, c0 + n]` up by `o`. -/
def fL (c0 n o k : Nat) : Nat := if c0 + o ≤ k ∧ k ≤ c0 + n + o then k - o else k

/-- A move loop at slot level: slots `[c0 + o, c0 + n + o]` take the slots `o` below them, the others keep. -/
theorem loop_slots {im : Image} {head : Nat} (o c0 n : Nat) (hstep : StepOK im head (16 * o)) (ho : 1 ≤ o)
    (hc0 : 13 ≤ c0) (hb : c0 + n + o < 332) (s : MachineState) (hpc : s.pc = pcOf head)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * (c0 + n)))
    (h30 : s.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * c0)) :
    ∃ t, Steps im s (6 * (n + 1)) (6 * (n + 1)) t ∧ t.pc = pcOf (head + 6) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧
      (∀ k w, k < 332 → w < 2 → t.getMem (slotA k w) =
        s.getMem (slotA (fL c0 n o k) w)) ∧
      Frame s t (fun X => 0x70d0 ≤ X ∧ X < 0x84c0) := by
  obtain ⟨t, st, pt, mt, rt, ft⟩ := move_loop hstep (by omega) n s (0x7000 + 16 * c0) (by omega) (by omega)
    (by omega) hpc (by rw [h28]; congr 1; omega) h30
  refine ⟨t, st, pt, rt, ?_, ft.mono (fun X _ h => by omega)⟩
  intro k w hk hw
  unfold slotA fL
  split_ifs with hin
  · obtain ⟨a, b⟩ := mt (k - o - c0) (by omega)
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · rw [show 0x7000 + 16 * k + 8 * 0 = 0x7000 + 16 * c0 + 16 * (k - o - c0) + 16 * o by omega, a]
      congr 2; omega
    · rw [show 0x7000 + 16 * k + 8 * 1 = 0x7000 + 16 * c0 + 16 * (k - o - c0) + 16 * o + 8 by omega, b]
      congr 2; omega
  · exact ft.get (by omega) (by omega)

def codeS54672 : List (BitVec 32) := (t51Code.drop 496).take 4
theorem codeAt_S54672 : CodeAt Images.expandImage (pcOf 54672) codeS54672 :=
  codeAt_t51_at 54672 (by decide) (by decide) (by decide)
sym_block eS54672 := symRun { noAlias := true } codeS54672 (pcOf 54672) 10

theorem setup54672 (s : MachineState) (hpc : s.pc = pcOf 54672) :
    ∃ t, Steps Images.expandImage s 4 4 t ∧ t.pc = pcOf 54676 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 175) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 88) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54672 codeAt_S54672 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

def codeS54682 : List (BitVec 32) := (t51Code.drop 506).take 4
theorem codeAt_S54682 : CodeAt Images.expandImage (pcOf 54682) codeS54682 :=
  codeAt_t51_at 54682 (by decide) (by decide) (by decide)
sym_block eS54682 := symRun { noAlias := true } codeS54682 (pcOf 54682) 10

theorem setup54682 (s : MachineState) (hpc : s.pc = pcOf 54682) :
    ∃ t, Steps Images.expandImage s 4 4 t ∧ t.pc = pcOf 54686 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 87) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 63) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54682 codeAt_S54682 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

def codeS54692 : List (BitVec 32) := (t51Code.drop 516).take 4
theorem codeAt_S54692 : CodeAt Images.expandImage (pcOf 54692) codeS54692 :=
  codeAt_t51_at 54692 (by decide) (by decide) (by decide)
sym_block eS54692 := symRun { noAlias := true } codeS54692 (pcOf 54692) 10

theorem setup54692 (s : MachineState) (hpc : s.pc = pcOf 54692) :
    ∃ t, Steps Images.expandImage s 4 4 t ∧ t.pc = pcOf 54696 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 62) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 38) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54692 codeAt_S54692 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

def codeS54702 : List (BitVec 32) := (t51Code.drop 526).take 4
theorem codeAt_S54702 : CodeAt Images.expandImage (pcOf 54702) codeS54702 :=
  codeAt_t51_at 54702 (by decide) (by decide) (by decide)
sym_block eS54702 := symRun { noAlias := true } codeS54702 (pcOf 54702) 10

theorem setup54702 (s : MachineState) (hpc : s.pc = pcOf 54702) :
    ∃ t, Steps Images.expandImage s 4 4 t ∧ t.pc = pcOf 54706 ∧
      t.getReg .x28 = BitVec.ofNat 64 (0x7000 + 16 * 37) ∧ t.getReg .x30 = BitVec.ofNat 64 (0x7000 + 16 * 13) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eS54702 codeAt_S54702 s hpc trivial, rfl, rfl, rfl, ?_, fun _ _ _ => rfl⟩
  intro r hr
  rw [Result.toState_getReg]
  cases r <;> first | exact (hr (by decide)).elim | rfl

/-! ## D6 (zero slots, sibling, cleanup, `j 1`) -/
def codeD6 : List (BitVec 32) := (t51Code.drop 536).take 27
theorem codeAt_D6 : CodeAt Images.expandImage (pcOf 54712) codeD6 :=
  codeAt_t51_at 54712 (by decide) (by decide) (by decide)
sym_block eD6 := symRun { noAlias := true } codeD6 (pcOf 54712) 100

/-- The 7 unused slots of the inflated layout. -/
def dummySlot (k : Nat) : Prop := k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183
instance (k : Nat) : Decidable (dummySlot k) := by unfold dummySlot; infer_instance

theorem d6_spec (s : MachineState) (hpc : s.pc = pcOf 54712) :
    ∃ t, Steps Images.expandImage s 27 27 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k w, k < 332 → w < 2 → t.getMem (slotA k w) =
        if dummySlot k then 0 else if k = 180 then (if w = 0 then s.getReg .x19 else s.getReg .x20)
        else s.getMem (slotA k w)) ∧
      Frame s t (fun X => 0x70d0 ≤ X ∧ X < 0x84c0) := by
  refine ⟨_, symRun_sound eD6 codeAt_D6 s hpc (by simp [eD6.res, rv_simp]),
    rfl, ?_, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rw [Result.toState_getReg]
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro k w hk hw
    simp only [Result.toState_getMem, eD6.res, slotA]
    t3n []
    rw [Nat.mod_eq_of_lt (show 0x7000 + 16 * k + 8 * w < 18446744073709551616 by omega)]
    by_cases hs : k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 180 ∨ k = 181 ∨ k = 182 ∨ k = 183
    · obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
      all_goals (rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [dummySlot])
    · iterate 16 rw [if_neg (by omega)]
      rw [if_neg (show ¬ dummySlot k by unfold dummySlot; omega), if_neg (by omega)]
  · intro X hX hn
    simp only [Result.toState_getMem, eD6.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show X < 18446744073709551616 by simpa using hX)]
    iterate 16 rw [if_neg (by omega)]

/-! ## DEC, composed -/
/-- The compact slot whose (D1-cleared) contents end up in slot `k` (`k` not unused, `k ≠ 180`). -/
def srcK (k : Nat) : Nat :=
  if k < 13 then k else if k < 39 then k - 1 else if k < 65 then k - 2 else if k < 91 then k - 3
  else if k < 180 then k - 4 else k - 8

theorem srcK_comp (k : Nat) (hk : k < 332) (hd : ¬ dummySlot k) (h180 : k ≠ 180) :
    fL 176 147 8 (fL 88 87 4 (fL 63 24 3 (fL 38 24 2 (fL 13 24 1 k)))) = srcK k := by
  unfold dummySlot at hd
  simp only [fL, srcK]
  split_ifs <;> omega

theorem frame_slot {s t : MachineState} (f : Frame s t (fun _ => False)) (k w : Nat) (hk : k < 332) (hw : w < 2) :
    t.getMem (slotA k w) = s.getMem (slotA k w) := f.get (by omega) id

theorem fL_le (c0 n o k : Nat) : fL c0 n o k ≤ k := by unfold fL; split_ifs <;> omega

/-- DEC output: slot `k`, word `w`, as a function of the memory `M` at DEC entry. -/
def decOut (M : Word → Word) (k w : Nat) : Word :=
  if dummySlot k then 0
  else if k = 180 then (if w = 0 then M (BitVec.ofNat 64 0x8440) else sibHi (M (BitVec.ofNat 64 0x8448)) (xD M))
  else d1Mem M (slotA (srcK k) w)

theorem d1Mem_frame (M : Word → Word) (A : Nat) (hA : A < 2 ^ 64) (h1 : A ≠ 417792)
    (h2 : A < 31368 ∨ 31480 < A) : d1Mem M (BitVec.ofNat 64 A) = M (BitVec.ofNat 64 A) := by
  unfold d1Mem aH pH
  rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega)]

/-- DEC from its entry (2,005 steps): the inflated layout (`decOut`), the hint at `0x66000`, the temporaries
zeroed, word 1 next; only the hint word and `[0x70d0, 0x84c0)` are written. -/
theorem dec_run (s : MachineState) (hpc : s.pc = pcOf 54569) (hh : (xD s.getMem >>> 16).toNat < 7744) :
    ∃ t, Steps Images.expandImage s 2005 2005 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6, .x7, .x18, .x19, .x20, .x28, .x29, .x30] ∧
      (∀ k w, k < 332 → w < 2 → t.getMem (slotA k w) = decOut s.getMem k w) ∧
      t.getMem (BitVec.ofNat 64 417792) = xD s.getMem >>> 16 ∧
      Frame s t (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, st1, pc1, x18_1, r1, m1⟩ := d1_spec s hpc
  rw [if_pos hh] at pc1
  obtain ⟨s2, st2, pc2, x19_2, x20_2, x28_2, x30_2, r2, f2⟩ := d3_spec s1 pc1
  obtain ⟨s3, st3, pc3, r3, m3, f3⟩ := loop_slots 8 176 147 stepL1 (by omega) (by omega) (by omega) s2 pc2 x28_2 x30_2
  obtain ⟨s4, st4, pc4, x28_4, x30_4, r4, f4⟩ := setup54672 s3 (by rw [pc3])
  obtain ⟨s5, st5, pc5, r5, m5, f5⟩ := loop_slots 4 88 87 stepL2 (by omega) (by omega) (by omega) s4 pc4
    (by rw [x28_4]) x30_4
  obtain ⟨s6, st6, pc6, x28_6, x30_6, r6, f6⟩ := setup54682 s5 (by rw [pc5])
  obtain ⟨s7, st7, pc7, r7, m7, f7⟩ := loop_slots 3 63 24 stepL3 (by omega) (by omega) (by omega) s6 pc6
    (by rw [x28_6]) x30_6
  obtain ⟨s8, st8, pc8, x28_8, x30_8, r8, f8⟩ := setup54692 s7 (by rw [pc7])
  obtain ⟨s9, st9, pc9, r9, m9, f9⟩ := loop_slots 2 38 24 stepL4 (by omega) (by omega) (by omega) s8 pc8
    (by rw [x28_8]) x30_8
  obtain ⟨s10, st10, pc10, x28_10, x30_10, r10, f10⟩ := setup54702 s9 (by rw [pc9])
  obtain ⟨s11, st11, pc11, r11, m11, f11⟩ := loop_slots 1 13 24 stepL5 (by omega) (by omega) (by omega) s10 pc10
    (by rw [x28_10]) x30_10
  obtain ⟨t, st12, pc12, z12, r12, m12, f12⟩ := d6_spec s11 (by rw [pc11])
  -- frames after D1
  have fA : Frame s2 s11 (fun X => 0x70d0 ≤ X ∧ X < 0x84c0) :=
    ((((((((f3.trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).mono
      (fun X _ h => by
        rcases h with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) <;> first | exact h | exact h.elim)
  have regs11 : RegsExcept s2 s11 [.x6, .x7, .x28, .x30] :=
    ((((((((r3.trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans r10).trans r11).mono
      (by intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  refine ⟨t, ?_, pc12, z12, ?_, ?_, ?_, ?_⟩
  · exact (((((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans
      st10).trans st11).trans st12).of_eq (by norm_num) (by norm_num)
  · exact ((r1.trans (r2.trans (regs11.trans r12)))).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto)
  · intro k w hk hw
    rw [m12 k w hk hw]
    unfold decOut
    split_ifs with hd h180 hw0
    · rfl
    · rw [regs11.get (by decide), x19_2, m1, d1Mem_frame _ _ (by decide) (by decide) (by decide)]
    · rw [regs11.get (by decide), x20_2, m1, d1Mem_frame _ _ (by decide) (by decide) (by decide), x18_1]
    · have hk5 := fL_le 13 24 1 k
      have hk4 := fL_le 38 24 2 (fL 13 24 1 k)
      have hk3 := fL_le 63 24 3 (fL 38 24 2 (fL 13 24 1 k))
      have hk2 := fL_le 88 87 4 (fL 63 24 3 (fL 38 24 2 (fL 13 24 1 k)))
      rw [m11 k w hk hw, frame_slot f10 _ w (by omega) hw,
        m9 _ w (by omega) hw, frame_slot f8 _ w (by omega) hw,
        m7 _ w (by omega) hw, frame_slot f6 _ w (by omega) hw,
        m5 _ w (by omega) hw, frame_slot f4 _ w (by omega) hw,
        m3 _ w (by omega) hw, srcK_comp k hk hd h180, frame_slot f2 _ w (by unfold srcK; split_ifs <;> omega) hw, m1]
  · have e : t.getMem (BitVec.ofNat 64 417792) = s2.getMem (BitVec.ofNat 64 417792) :=
      (f12.get (by decide) (by omega)).trans (fA.get (by decide) (by omega))
    rw [e, f2.get (by decide) id, m1]
    rfl
  · have f1 : Frame s s1 (fun A => A = 417792 ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
      intro A hA hn
      rw [m1, d1Mem_frame _ _ hA (by omega) (by omega)]
    exact ((((f1.trans f2).trans fA).trans f12).mono (fun X _ h => by
      rcases h with ((h | h) | h) | h <;> first | exact h | exact h.elim | exact Or.inr h))

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_PrePassByte ====
section

/-! # DEC at signature level

If the 5,195-byte signature `b` sits at `0x7000` (`SigMem`), DEC's accumulator is the codec's `xOfB b`, the hint it
stores is `(sigDecC b).policyHints`, and its output slots are the inflated layout
`SharedCodec.inflatedRead 0 (SharedCodec.digC b)`. -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
open SigGolfCandidate.T3 (topZeroBits topZeroAlloc)
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-- The DEC entry memory holds the 5,195-byte signature at `0x7000` (649 full dwords + 3 tail bytes). -/
structure SigMem (M : Word → Word) (b : SharedCodec.CBytes) : Prop where
  word : ∀ j, j < 649 → M (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64
  tail : (M (BitVec.ofNat 64 0x8448)).toNat % 2 ^ 24 = b.toNat / 2 ^ (64 * 649) % 2 ^ 24

theorem cDig_word (b : SharedCodec.CBytes) (c w : Nat) (hw : w < 2) :
    (SharedCodec.cDig b c).extractLsb' (64 * w) 64 = b.extractLsb' (64 * (2 * c + w)) 64 := by
  unfold SharedCodec.cDig
  rw [SharedCodec.extract_digest_word b (128 * c) w hw]
  congr 1
  omega

theorem slot_word {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (c w : Nat) (hc : c < 324)
    (hw : w < 2) : M (slotA c w) = (SharedCodec.cDig b c).extractLsb' (64 * w) 64 := by
  rw [cDig_word b c w hw, ← h.word (2 * c + w) (by omega)]
  unfold slotA
  congr 2
  omega

theorem topBits_cDig (b : SharedCodec.CBytes) (c n : Nat) (hn : n ≤ 64) :
    SharedCodec.topBits n (SharedCodec.cDig b c) = (b.extractLsb' (64 * (2 * c + 1)) 64).toNat / 2 ^ (64 - n) := by
  unfold SharedCodec.topBits SharedCodec.cDig
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  generalize b.toNat = x
  rw [show 64 * (2 * c + 1) = 128 * c + 64 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x / 2 ^ (128 * c) = y
  rw [show 128 - n = 64 + (64 - n) by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  congr 1
  rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]

theorem aH_word {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (j : Nat) (hj : j ≤ 10) :
    M (aH j) = b.extractLsb' (64 * (2 * (165 + j) + 1)) 64 := by
  rw [← h.word _ (by omega)]
  unfold aH pH
  congr 2
  omega

theorem xD_xOfB {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    (xD M).toNat = SharedCodec.xOfB b := by
  rw [xD_toNat]
  unfold xN SharedCodec.xOfB
  rw [topBits_cDig b 168 1 (by omega), topBits_cDig b 169 1 (by omega), topBits_cDig b 170 2 (by omega),
    topBits_cDig b 171 3 (by omega), topBits_cDig b 172 4 (by omega), topBits_cDig b 173 5 (by omega),
    topBits_cDig b 174 6 (by omega), topBits_cDig b 175 7 (by omega),
    aH_word h 3 (by omega), aH_word h 4 (by omega), aH_word h 5 (by omega), aH_word h 6 (by omega),
    aH_word h 7 (by omega), aH_word h 8 (by omega), aH_word h 9 (by omega), aH_word h 10 (by omega)]

theorem hint_toNat {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    (xD M >>> 16).toNat = (SharedCodec.sigDecC b).policyHints.toNat := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, xD_xOfB h]
  show _ = (BitVec.ofNat 16 (SharedCodec.xOfB b / 2 ^ 16)).toNat
  have := SharedCodec.xOfB_lt b
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem hint_eq {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) :
    xD M >>> 16 = BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat := by
  apply BitVec.eq_of_toNat_eq
  have := ((SharedCodec.sigDecC b).policyHints).isLt
  rw [hint_toNat h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem clearTop_lo (t : Nat) (ht : t ≤ 64) (d : SigGolfCandidate.T3.Digest) :
    (SharedCodec.clearTop t d).extractLsb' (64 * 0) 64 = d.extractLsb' (64 * 0) 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold SharedCodec.clearTop
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mul_zero, Nat.shiftRight_zero,
    Nat.shiftRight_zero]
  rw [Nat.mod_eq_of_lt (show d.toNat % 2 ^ (128 - t) < 2 ^ 128 from
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega))),
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem clearTop_hi (t : Nat) (ht : t ≤ 64) (d : SigGolfCandidate.T3.Digest) :
    ((SharedCodec.clearTop t d).extractLsb' (64 * 1) 64).toNat = (d.extractLsb' (64 * 1) 64).toNat % 2 ^ (64 - t) := by
  unfold SharedCodec.clearTop
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show d.toNat % 2 ^ (128 - t) < 2 ^ 128 from
    lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega)))]
  rw [show 128 - t = 64 + (64 - t) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 - t ≤ 64))]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by omega) (by omega)))

theorem d1Mem_lo (M : Word → Word) (A : Nat) (hA : A < 0x84c0) (h16 : A % 16 = 0) :
    d1Mem M (BitVec.ofNat 64 A) = M (BitVec.ofNat 64 A) := by
  unfold d1Mem aH pH
  rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega),
    if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by rw [ofNat_eq_iff]; omega)]

theorem d1Mem_aH (M : Word → Word) (j : Nat) (h3 : 3 ≤ j) (h10 : j ≤ 10) :
    d1Mem M (aH j) = clr (topZeroBits j) (M (aH j)) := by
  interval_cases j <;> simp [d1Mem, aH, pH, topZeroBits, topZeroAlloc]

theorem internalDummy_iff (k : Nat) : SharedCodec.internalDummy k = true ↔ dummySlot k := by
  simp [SharedCodec.internalDummy, dummySlot]

theorem zero_extract (w : Nat) : (0 : SigGolfCandidate.T3.Digest).extractLsb' (64 * w) 64 = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- DEC's output slots are the inflated layout of the decoded signature. -/
theorem decOut_eq {M : Word → Word} {b : SharedCodec.CBytes} (h : SigMem M b) (k w : Nat) (hk : k < 332)
    (hw : w < 2) :
    decOut M k w = (SharedCodec.inflatedRead (0 : SigGolfCandidate.T3.Digest) (SharedCodec.digC b) k).extractLsb' (64 * w) 64 := by
  by_cases hd : dummySlot k
  · have e : decOut M k w = 0 := by unfold decOut; rw [if_pos hd]
    rw [e, SharedCodec.inflatedRead, if_pos ((internalDummy_iff k).mpr hd), zero_extract]
  have hnd : ¬ (SharedCodec.internalDummy k = true) := fun h => hd ((internalDummy_iff k).mp h)
  rw [SharedCodec.inflatedRead, if_neg hnd]
  by_cases h180 : k = 180
  · have e : decOut M k w = (if w = 0 then M (BitVec.ofNat 64 0x8440)
        else sibHi (M (BitVec.ofNat 64 0x8448)) (xD M)) := by
      unfold decOut; rw [if_neg hd, if_pos h180]
    rw [e, h180, show SharedCodec.externalFullIndex 180 = 176 from rfl]
    have hd176 : SharedCodec.digC b 176 = BitVec.ofNat 128 (b.toNat / 2 ^ (64 * 648) % 2 ^ 88 +
        SharedCodec.xOfB b % 2 ^ 16 * 2 ^ 88) := by
      unfold SharedCodec.digC; rw [if_neg (by omega), if_pos rfl]
    rw [hd176]
    apply BitVec.eq_of_toNat_eq
    have hX := SharedCodec.xOfB_lt b
    have hw648 := h.word 648 (by omega)
    have ht := h.tail
    have hsplit : b.toNat / 2 ^ (64 * 649) = b.toNat / 2 ^ (64 * 648) / 2 ^ 64 := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    rw [hsplit] at ht
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · rw [if_pos rfl, show (BitVec.ofNat 64 0x8440 : Word) = BitVec.ofNat 64 (0x7000 + 8 * 648) from rfl, hw648,
        BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
        Nat.shiftRight_eq_div_pow]
      generalize b.toNat / 2 ^ (64 * 648) = T
      generalize SharedCodec.xOfB b = X at hX
      norm_num
      omega
    · rw [if_neg (by omega), sibHi_toNat, ht, xD_xOfB h, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow]
      generalize b.toNat / 2 ^ (64 * 648) = T
      generalize SharedCodec.xOfB b = X at hX
      norm_num
      omega
  have e : decOut M k w = d1Mem M (slotA (srcK k) w) := by unfold decOut; rw [if_neg hd, if_neg h180]
  rw [e]
  have hk' : ¬ (k = 13 ∨ k = 39 ∨ k = 65 ∨ k = 91 ∨ k = 181 ∨ k = 182 ∨ k = 183) := hd
  by_cases hA : k < 170
  · have he : SharedCodec.externalFullIndex k = srcK k := by
      unfold SharedCodec.externalFullIndex srcK; split_ifs <;> omega
    have hs : srcK k < 166 := by unfold srcK; split_ifs <;> omega
    rw [he]
    have hdig : SharedCodec.digC b (srcK k) = SharedCodec.cDig b (srcK k) := by
      unfold SharedCodec.digC; rw [if_pos (by omega), if_neg (by omega)]
    rw [hdig, ← slot_word h _ w (by omega) hw]
    unfold slotA
    rw [d1Mem_frame _ _ (by omega) (by omega) (by omega)]
  by_cases hB : k < 180
  · have he : SharedCodec.externalFullIndex k = k - 4 := by
      unfold SharedCodec.externalFullIndex; split_ifs <;> omega
    have hs : srcK k = k - 4 := by unfold srcK; split_ifs <;> omega
    rw [he, hs]
    have hdig : SharedCodec.digC b (k - 4) =
        SharedCodec.clearTop (topZeroBits (k - 4 - 165)) (SharedCodec.cDig b (k - 4)) := by
      unfold SharedCodec.digC; rw [if_pos (by omega), if_pos (by omega)]
    rw [hdig]
    have htz : topZeroBits (k - 4 - 165) ≤ 64 := by
      unfold topZeroBits topZeroAlloc
      have : k - 4 - 165 < 11 := by omega
      interval_cases (k - 4 - 165) <;> decide
    obtain rfl | rfl : w = 0 ∨ w = 1 := by omega
    · rw [clearTop_lo _ htz, ← slot_word h _ 0 (by omega) (by omega)]
      unfold slotA
      rw [d1Mem_lo _ _ (by omega) (by omega)]
    · apply BitVec.eq_of_toNat_eq
      rw [clearTop_hi _ htz, ← slot_word h _ 1 (by omega) (by omega)]
      by_cases hj : k < 172
      · have h0 : topZeroBits (k - 4 - 165) = 0 := by
          unfold topZeroBits topZeroAlloc
          have : k - 4 - 165 = 1 ∨ k - 4 - 165 = 2 := by omega
          rcases this with h | h <;> rw [h] <;> rfl
        rw [h0]
        unfold slotA
        rw [d1Mem_frame _ _ (by omega) (by omega) (by omega), Nat.sub_zero,
          Nat.mod_eq_of_lt (BitVec.isLt _)]
      · have ha : slotA (k - 4) 1 = aH (k - 4 - 165) := by
          unfold slotA aH pH; congr 1; omega
        rw [ha, d1Mem_aH _ _ (by omega) (by omega), clr_toNat _ htz]
  · have h184 : 184 ≤ k := by omega
    have he : SharedCodec.externalFullIndex k = k - 7 := by
      unfold SharedCodec.externalFullIndex; split_ifs <;> omega
    have hs : srcK k = k - 8 := by unfold srcK; split_ifs <;> omega
    rw [he, hs]
    have hdig : SharedCodec.digC b (k - 7) = SharedCodec.cDig b (k - 8) := by
      unfold SharedCodec.digC; rw [if_neg (by omega), if_neg (by omega), show k - 7 - 1 = k - 8 by omega]
    rw [hdig, ← slot_word h _ w (by omega) hw]
    unfold slotA
    rw [d1Mem_frame _ _ (by omega) (by omega) (by omega)]

end ClaudeWCT.W9.Machine.Expand.PrePass
end
-- ==== merged from T3M_Search_ProducerData ====
section

namespace SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3M.Images
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Check a byte slice once, then recover its indexed specification without repeated list traversal. -/
private theorem getD_slice_of_eq (xs : List (BitVec 8)) (start count : Nat)
    (f : Nat → BitVec 8)
    (h : (xs.drop start).take count = List.ofFn (fun i : Fin count => f (start + i.val)))
    (i : Nat) (hi : i < count) : xs.getD (start + i) 0 = f (start + i) := by
  have he := congrArg (fun ys : List (BitVec 8) => ys[i]?) h
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop, List.getElem?_ofFn, dif_pos hi] at he
  rw [List.getD_eq_getElem?_getD, he]
  rfl

-- Keep the zero offset explicit so elaboration matches the slice lemma without normalizing the table.
private theorem sign_table_check : (signLegacyData.drop 0).take 628 =
    List.ofFn (fun i : Fin 628 => tableByte (0 + i.val)) := by
  decide +kernel
private theorem expand_table_check : (expandLegacyData.drop 0).take 628 =
    List.ofFn (fun i : Fin 628 => tableByte (0 + i.val)) := by
  decide +kernel
theorem signLegacyData_table (i : Nat) (hi : i < 628) : signLegacyData.getD i 0 = tableByte i := by
  simpa only [Nat.zero_add] using getD_slice_of_eq signLegacyData 0 628 tableByte sign_table_check i hi
theorem expandLegacyData_table (i : Nat) (hi : i < 628) : expandLegacyData.getD i 0 = tableByte i := by
  simpa only [Nat.zero_add] using getD_slice_of_eq expandLegacyData 0 628 tableByte expand_table_check i hi

private theorem expand_cf_check : (expandLegacyData.drop 628).take 20 =
    List.ofFn (fun j : Fin 20 => cfByte 0 (628 + j.val)) := by
  decide +kernel
theorem expandLegacyData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) : expandLegacyData.getD i 0 = cfByte 0 i := by
  have h := getD_slice_of_eq expandLegacyData 628 20 (cfByte 0) expand_cf_check (i-628) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signLegacyData_length : signLegacyData.length = 4096 := by decide +kernel
theorem expandLegacyData_length : expandLegacyData.length = 4096 := by decide +kernel
theorem getD_prefixed (pre tail : List (BitVec 8)) (n i : Nat)
    (hp : pre.length = n) :
    (pre ++ tail).getD (n + i) 0 = tail.getD i 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hp, Nat.add_sub_cancel_left]
  rfl
theorem signData_length : signData.length = 86144 := Images.signData_length
theorem signZtData_length : signZtData.length = 128 := by decide +kernel
theorem signData_table (i : Nat) (hi : i < 628) :
    signData.getD (82048 + i) 0 = tableByte i := by
  rw [signData, show 82048 + i = 128 + (81920 + i) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_table i hi
private theorem zt_check : ∀ r : Fin 128, signZtData.getD r.val 0 = ZeroCap.ztByte r.val := by decide +kernel
/-- The zero-count table at the start of the sign data. -/
theorem signData_zt (r : Nat) (hr : r < 128) : signData.getD r 0 = ZeroCap.ztByte r := by
  rw [signData, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [signZtData_length]; exact hr),
    ← List.getD_eq_getElem?_getD]
  exact zt_check ⟨r, hr⟩
theorem expandData_length : expandData.length = 29936 := Images.expandData_length
theorem expandZtData_length : expandZtData.length = 128 := by decide +kernel
theorem expandData_cf (i : Nat) (hi : 628 ≤ i) (hj : i < 648) :
    expandData.getD (25840 + i) 0 = cfByte 0 i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_cf i hi hj
theorem expandData_table (i : Nat) (hi : i < 628) :
    expandData.getD (25840 + i) 0 = tableByte i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_table i hi


private theorem expand_reward_check :
    (expandLegacyData.drop 1024).take 1920 =
      List.ofFn (fun j : Fin 1920 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
theorem expandLegacyData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    expandLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq expandLegacyData 1024 1920 Reward.rewardTableByte expand_reward_check
    (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem expandData_reward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2944) :
    expandData.getD (25840 + i) 0 = Reward.rewardTableByte i := by
  rw [expandData, List.append_assoc, show 25840 + i = 128 + (2160 + (23552 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length, getD_prefixed _ _ _ _ expandPrefixData_length]
  exact expandLegacyData_reward i hi hj

/-! ### Campaign T51 sign-data facts (the T51 sign image: TOP_DATA + 632..647 = T51 dummy word, TOP_DATA + 2048..3939
= the 1892-byte T51 packed block; the lower reward tables 1024..2047 and the flag byte 631 unchanged) -/
private theorem sign_flag_check : signLegacyData.getD 631 0 = BitVec.ofNat 8 1 := by decide +kernel
theorem signLegacyData_flag : signLegacyData.getD 631 0 = BitVec.ofNat 8 1 := sign_flag_check
theorem signData_flag : signData.getD (82048 + 631) 0 = BitVec.ofNat 8 1 := by
  rw [signData, show 82048 + 631 = 128 + (81920 + 631) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_flag
private theorem sign_lower_check :
    (signLegacyData.drop 1024).take 1024 =
      List.ofFn (fun j : Fin 1024 => Reward.rewardTableByte (1024 + j.val)) := by
  decide +kernel
theorem signLegacyData_lowerReward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2048) :
    signLegacyData.getD i 0 = Reward.rewardTableByte i := by
  have h := getD_slice_of_eq signLegacyData 1024 1024 Reward.rewardTableByte sign_lower_check (i-1024) (by omega)
  simpa only [Nat.add_sub_of_le hi] using h
theorem signData_lowerReward (i : Nat) (hi : 1024 ≤ i) (hj : i < 2048) :
    signData.getD (82048+i) 0 = Reward.rewardTableByte i := by
  rw [signData, show 82048 + i = 128 + (81920 + i) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_lowerReward i hi hj
private theorem sign_t51_check :
    (signLegacyData.drop 2048).take 1892 = List.ofFn (fun j : Fin 1892 => T51.tByte (2048 + j.val - 2048)) := by
  decide +kernel
/-- The T51 packed table block in the sign image (TOP_DATA + 2048 = 0xFFF800). -/
theorem signLegacyData_t51 (i : Nat) (hi : i < 1892) : signLegacyData.getD (2048 + i) 0 = T51.tByte i := by
  have h := getD_slice_of_eq signLegacyData 2048 1892 (fun j => T51.tByte (j - 2048)) sign_t51_check i hi
  rw [h, Nat.add_sub_cancel_left]
theorem signData_t51 (i : Nat) (hi : i < 1892) : signData.getD (82048 + 2048 + i) 0 = T51.tByte i := by
  rw [signData, show 82048 + 2048 + i = 128 + (81920 + (2048 + i)) by omega, getD_prefixed _ _ _ _ signZtData_length,
    getD_prefixed _ _ _ _ signPrefixData_length]; exact signLegacyData_t51 i hi
/-! ### Campaign T51 expand-data fact: the 1892-byte T51 packed block at `0xFF9E00 = DB0 + 4848` (expand data offset
4848 = 128 Zt + 2160 shared + 2560 into the prefix data), the source of the expand's KCOPY (-> RAM `0xA0000`). -/
private theorem expand_t51_check :
    ((expandPrefixData ++ expandLegacyData).drop 2560).take 1892 =
      List.ofFn (fun j : Fin 1892 => T51.tByte (2560 + j.val - 2560)) := by
  decide +kernel
theorem expandData_t51 (i : Nat) (hi : i < 1892) : expandData.getD (4848 + i) 0 = T51.tByte i := by
  rw [expandData, List.append_assoc, show 4848 + i = 128 + (2160 + (2560 + i)) from by omega,
    getD_prefixed _ _ _ _ expandZtData_length, getD_prefixed _ _ _ _ expandSharedData_length]
  have h := getD_slice_of_eq (expandPrefixData ++ expandLegacyData) 2560 1892 (fun j => T51.tByte (j - 2560))
    expand_t51_check i hi
  rw [h, Nat.add_sub_cancel_left]

end SigGolfCandidate.T3M.Search
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_Data ====
section

set_option maxRecDepth 100000
namespace ClaudeWCT.W9.Machine.Sign
def signCodeSha256 : String := "45cd5ad1942a2f5a18141fd2c523be1247258a9b82a126e72493c04ecf3c014a"
def signDataSha256 : String := "5ecc152d935566937ca8f089f73f3de78454201fe16fa3386fc250313cbe86b8"
def signNewSha256 : String := "9f086e17a1eb08fd78835447de8db8ec7ddfc443d301c58db04f800691c6adec"
def costSha256 : String := "00bf597fe1b13081d81fc595aaf5c6aa5560f46bfcb40984ec2c5c3ad1f9e059"
def tblSha256 : String := "a5bd80888b91939363ce3fc8852c9bd1d9d8f5854197ccc4eb958fb0f7818d9d"
def headCode_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_42).drop 251,(SigGolfCandidate.T3M.Images.signReferenceCode_43).take 178].flatten
def headCode : List (BitVec 32) := headCode_0
def coordCode0_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_43).drop 178,(SigGolfCandidate.T3M.Images.signReferenceCode_44).take 178].flatten
def coordCode0_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_44).drop 178,(SigGolfCandidate.T3M.Images.signReferenceCode_45).take 178].flatten
def coordCode0_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_45).drop 178,(SigGolfCandidate.T3M.Images.signReferenceCode_46).take 178].flatten
def coordCode0_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_46).drop 178,(SigGolfCandidate.T3M.Images.signReferenceCode_47).take 178].flatten
def coordCode0_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_47).drop 178).take 28
def coordCode0 : List (BitVec 32) := coordCode0_0 ++ coordCode0_1 ++ coordCode0_2 ++ coordCode0_3 ++ coordCode0_4
def coordCode1_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_47).drop 206,(SigGolfCandidate.T3M.Images.signReferenceCode_48).take 206].flatten
def coordCode1_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_48).drop 206,(SigGolfCandidate.T3M.Images.signReferenceCode_49).take 206].flatten
def coordCode1_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_49).drop 206,(SigGolfCandidate.T3M.Images.signReferenceCode_50).take 206].flatten
def coordCode1_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_50).drop 206,(SigGolfCandidate.T3M.Images.signReferenceCode_51).take 206].flatten
def coordCode1_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_51).drop 206).take 35
def coordCode1 : List (BitVec 32) := coordCode1_0 ++ coordCode1_1 ++ coordCode1_2 ++ coordCode1_3 ++ coordCode1_4
def coordCode2_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_51).drop 241,(SigGolfCandidate.T3M.Images.signReferenceCode_52).take 241].flatten
def coordCode2_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_52).drop 241,(SigGolfCandidate.T3M.Images.signReferenceCode_53).take 241].flatten
def coordCode2_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_53).drop 241,(SigGolfCandidate.T3M.Images.signReferenceCode_54).take 241].flatten
def coordCode2_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_54).drop 241,(SigGolfCandidate.T3M.Images.signReferenceCode_55).take 241].flatten
def coordCode2_4 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_55).drop 241,(SigGolfCandidate.T3M.Images.signReferenceCode_56).take 21].flatten
def coordCode2 : List (BitVec 32) := coordCode2_0 ++ coordCode2_1 ++ coordCode2_2 ++ coordCode2_3 ++ coordCode2_4
def coordCode3_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_56).drop 21,(SigGolfCandidate.T3M.Images.signReferenceCode_57).take 21].flatten
def coordCode3_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_57).drop 21,(SigGolfCandidate.T3M.Images.signReferenceCode_58).take 21].flatten
def coordCode3_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_58).drop 21,(SigGolfCandidate.T3M.Images.signReferenceCode_59).take 21].flatten
def coordCode3_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_59).drop 21,(SigGolfCandidate.T3M.Images.signReferenceCode_60).take 21].flatten
def coordCode3_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_60).drop 21).take 36
def coordCode3 : List (BitVec 32) := coordCode3_0 ++ coordCode3_1 ++ coordCode3_2 ++ coordCode3_3 ++ coordCode3_4
def coordCode4_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_60).drop 57,(SigGolfCandidate.T3M.Images.signReferenceCode_61).take 57].flatten
def coordCode4_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_61).drop 57,(SigGolfCandidate.T3M.Images.signReferenceCode_62).take 57].flatten
def coordCode4_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_62).drop 57,(SigGolfCandidate.T3M.Images.signReferenceCode_63).take 57].flatten
def coordCode4_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_63).drop 57,(SigGolfCandidate.T3M.Images.signReferenceCode_64).take 57].flatten
def coordCode4_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_64).drop 57).take 35
def coordCode4 : List (BitVec 32) := coordCode4_0 ++ coordCode4_1 ++ coordCode4_2 ++ coordCode4_3 ++ coordCode4_4
def coordCode5_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_64).drop 92,(SigGolfCandidate.T3M.Images.signReferenceCode_65).take 92].flatten
def coordCode5_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_65).drop 92,(SigGolfCandidate.T3M.Images.signReferenceCode_66).take 92].flatten
def coordCode5_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_66).drop 92,(SigGolfCandidate.T3M.Images.signReferenceCode_67).take 92].flatten
def coordCode5_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_67).drop 92,(SigGolfCandidate.T3M.Images.signReferenceCode_68).take 92].flatten
def coordCode5_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_68).drop 92).take 36
def coordCode5 : List (BitVec 32) := coordCode5_0 ++ coordCode5_1 ++ coordCode5_2 ++ coordCode5_3 ++ coordCode5_4
def coordCode6_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_68).drop 128,(SigGolfCandidate.T3M.Images.signReferenceCode_69).take 128].flatten
def coordCode6_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_69).drop 128,(SigGolfCandidate.T3M.Images.signReferenceCode_70).take 128].flatten
def coordCode6_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_70).drop 128,(SigGolfCandidate.T3M.Images.signReferenceCode_71).take 128].flatten
def coordCode6_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_71).drop 128,(SigGolfCandidate.T3M.Images.signReferenceCode_72).take 128].flatten
def coordCode6_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_72).drop 128).take 36
def coordCode6 : List (BitVec 32) := coordCode6_0 ++ coordCode6_1 ++ coordCode6_2 ++ coordCode6_3 ++ coordCode6_4
def coordCode7_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_72).drop 164,(SigGolfCandidate.T3M.Images.signReferenceCode_73).take 164].flatten
def coordCode7_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_73).drop 164,(SigGolfCandidate.T3M.Images.signReferenceCode_74).take 164].flatten
def coordCode7_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_74).drop 164,(SigGolfCandidate.T3M.Images.signReferenceCode_75).take 164].flatten
def coordCode7_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_75).drop 164,(SigGolfCandidate.T3M.Images.signReferenceCode_76).take 164].flatten
def coordCode7_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_76).drop 164).take 35
def coordCode7 : List (BitVec 32) := coordCode7_0 ++ coordCode7_1 ++ coordCode7_2 ++ coordCode7_3 ++ coordCode7_4
def coordCode8_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_76).drop 199,(SigGolfCandidate.T3M.Images.signReferenceCode_77).take 199].flatten
def coordCode8_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_77).drop 199,(SigGolfCandidate.T3M.Images.signReferenceCode_78).take 199].flatten
def coordCode8_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_78).drop 199,(SigGolfCandidate.T3M.Images.signReferenceCode_79).take 199].flatten
def coordCode8_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_79).drop 199,(SigGolfCandidate.T3M.Images.signReferenceCode_80).take 199].flatten
def coordCode8_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_80).drop 199).take 36
def coordCode8 : List (BitVec 32) := coordCode8_0 ++ coordCode8_1 ++ coordCode8_2 ++ coordCode8_3 ++ coordCode8_4
/-- Campaign T51: the tail window of the CURRENT sign image (word 20731 `addi t3,t3,-1856`: compaction source 0x78C0,
SIG + 2240; #938 -1904). -/
def tailCode_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_80).drop 235,(SigGolfCandidate.T3M.Images.signCode_81).take 35].flatten
def tailCode : List (BitVec 32) := tailCode_0
def fieldIdx : List Nat := [11186,12238,13297,14357,15417,16476,17536,18596,19655]
def coordCodes : List (List (BitVec 32)) := [coordCode0, coordCode1, coordCode2, coordCode3, coordCode4, coordCode5, coordCode6, coordCode7, coordCode8]
/-- Witness stack (charge 86): the coordinate windows of the INSTALLED sign image (`signCode_*`; FTS chains 1, 3
call the G stubs at 21200 through `jal t3`). `coordCodes` keeps the reference image. -/
def coordCodeW0_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_43).drop 178,(SigGolfCandidate.T3M.Images.signCode_44).take 178].flatten
def coordCodeW0_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_44).drop 178,(SigGolfCandidate.T3M.Images.signCode_45).take 178].flatten
def coordCodeW0_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_45).drop 178,(SigGolfCandidate.T3M.Images.signCode_46).take 178].flatten
def coordCodeW0_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_46).drop 178,(SigGolfCandidate.T3M.Images.signCode_47).take 178].flatten
def coordCodeW0_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_47).drop 178).take 28
def coordCodeW0 : List (BitVec 32) := coordCodeW0_0 ++ coordCodeW0_1 ++ coordCodeW0_2 ++ coordCodeW0_3 ++ coordCodeW0_4
def coordCodeW1_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_47).drop 206,(SigGolfCandidate.T3M.Images.signCode_48).take 206].flatten
def coordCodeW1_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_48).drop 206,(SigGolfCandidate.T3M.Images.signCode_49).take 206].flatten
def coordCodeW1_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_49).drop 206,(SigGolfCandidate.T3M.Images.signCode_50).take 206].flatten
def coordCodeW1_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_50).drop 206,(SigGolfCandidate.T3M.Images.signCode_51).take 206].flatten
def coordCodeW1_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_51).drop 206).take 35
def coordCodeW1 : List (BitVec 32) := coordCodeW1_0 ++ coordCodeW1_1 ++ coordCodeW1_2 ++ coordCodeW1_3 ++ coordCodeW1_4
def coordCodeW2_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_51).drop 241,(SigGolfCandidate.T3M.Images.signCode_52).take 241].flatten
def coordCodeW2_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_52).drop 241,(SigGolfCandidate.T3M.Images.signCode_53).take 241].flatten
def coordCodeW2_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_53).drop 241,(SigGolfCandidate.T3M.Images.signCode_54).take 241].flatten
def coordCodeW2_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_54).drop 241,(SigGolfCandidate.T3M.Images.signCode_55).take 241].flatten
def coordCodeW2_4 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_55).drop 241,(SigGolfCandidate.T3M.Images.signCode_56).take 21].flatten
def coordCodeW2 : List (BitVec 32) := coordCodeW2_0 ++ coordCodeW2_1 ++ coordCodeW2_2 ++ coordCodeW2_3 ++ coordCodeW2_4
def coordCodeW3_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_56).drop 21,(SigGolfCandidate.T3M.Images.signCode_57).take 21].flatten
def coordCodeW3_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_57).drop 21,(SigGolfCandidate.T3M.Images.signCode_58).take 21].flatten
def coordCodeW3_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_58).drop 21,(SigGolfCandidate.T3M.Images.signCode_59).take 21].flatten
def coordCodeW3_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_59).drop 21,(SigGolfCandidate.T3M.Images.signCode_60).take 21].flatten
def coordCodeW3_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_60).drop 21).take 36
def coordCodeW3 : List (BitVec 32) := coordCodeW3_0 ++ coordCodeW3_1 ++ coordCodeW3_2 ++ coordCodeW3_3 ++ coordCodeW3_4
def coordCodeW4_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_60).drop 57,(SigGolfCandidate.T3M.Images.signCode_61).take 57].flatten
def coordCodeW4_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_61).drop 57,(SigGolfCandidate.T3M.Images.signCode_62).take 57].flatten
def coordCodeW4_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_62).drop 57,(SigGolfCandidate.T3M.Images.signCode_63).take 57].flatten
def coordCodeW4_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_63).drop 57,(SigGolfCandidate.T3M.Images.signCode_64).take 57].flatten
def coordCodeW4_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_64).drop 57).take 35
def coordCodeW4 : List (BitVec 32) := coordCodeW4_0 ++ coordCodeW4_1 ++ coordCodeW4_2 ++ coordCodeW4_3 ++ coordCodeW4_4
def coordCodeW5_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_64).drop 92,(SigGolfCandidate.T3M.Images.signCode_65).take 92].flatten
def coordCodeW5_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_65).drop 92,(SigGolfCandidate.T3M.Images.signCode_66).take 92].flatten
def coordCodeW5_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_66).drop 92,(SigGolfCandidate.T3M.Images.signCode_67).take 92].flatten
def coordCodeW5_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_67).drop 92,(SigGolfCandidate.T3M.Images.signCode_68).take 92].flatten
def coordCodeW5_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_68).drop 92).take 36
def coordCodeW5 : List (BitVec 32) := coordCodeW5_0 ++ coordCodeW5_1 ++ coordCodeW5_2 ++ coordCodeW5_3 ++ coordCodeW5_4
def coordCodeW6_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_68).drop 128,(SigGolfCandidate.T3M.Images.signCode_69).take 128].flatten
def coordCodeW6_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_69).drop 128,(SigGolfCandidate.T3M.Images.signCode_70).take 128].flatten
def coordCodeW6_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_70).drop 128,(SigGolfCandidate.T3M.Images.signCode_71).take 128].flatten
def coordCodeW6_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_71).drop 128,(SigGolfCandidate.T3M.Images.signCode_72).take 128].flatten
def coordCodeW6_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_72).drop 128).take 36
def coordCodeW6 : List (BitVec 32) := coordCodeW6_0 ++ coordCodeW6_1 ++ coordCodeW6_2 ++ coordCodeW6_3 ++ coordCodeW6_4
def coordCodeW7_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_72).drop 164,(SigGolfCandidate.T3M.Images.signCode_73).take 164].flatten
def coordCodeW7_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_73).drop 164,(SigGolfCandidate.T3M.Images.signCode_74).take 164].flatten
def coordCodeW7_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_74).drop 164,(SigGolfCandidate.T3M.Images.signCode_75).take 164].flatten
def coordCodeW7_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_75).drop 164,(SigGolfCandidate.T3M.Images.signCode_76).take 164].flatten
def coordCodeW7_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_76).drop 164).take 35
def coordCodeW7 : List (BitVec 32) := coordCodeW7_0 ++ coordCodeW7_1 ++ coordCodeW7_2 ++ coordCodeW7_3 ++ coordCodeW7_4
def coordCodeW8_0 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_76).drop 199,(SigGolfCandidate.T3M.Images.signCode_77).take 199].flatten
def coordCodeW8_1 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_77).drop 199,(SigGolfCandidate.T3M.Images.signCode_78).take 199].flatten
def coordCodeW8_2 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_78).drop 199,(SigGolfCandidate.T3M.Images.signCode_79).take 199].flatten
def coordCodeW8_3 : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signCode_79).drop 199,(SigGolfCandidate.T3M.Images.signCode_80).take 199].flatten
def coordCodeW8_4 : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_80).drop 199).take 36
def coordCodeW8 : List (BitVec 32) := coordCodeW8_0 ++ coordCodeW8_1 ++ coordCodeW8_2 ++ coordCodeW8_3 ++ coordCodeW8_4
def coordCodesW : List (List (BitVec 32)) := [coordCodeW0, coordCodeW1, coordCodeW2, coordCodeW3, coordCodeW4, coordCodeW5, coordCodeW6, coordCodeW7, coordCodeW8]
/-- Witness stack: the FTS G stubs at sign words 21200..21229 (interior at 21200, terminal at 21215). -/
def ftsStub : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signCode_82).drop 208).take 30
/-- Nested FTS (r1-1): the sign trampolines at words 21450..21666 (leaf pad, fold post-hash, forest replacement). -/
def signTramp : List (BitVec 32) := [(SigGolfCandidate.T3M.Images.signReferenceCode_83).drop 202,(SigGolfCandidate.T3M.Images.signReferenceCode_84).take 163].flatten

/-- C4 (FTS coordinate + 1, adapted from b3cc11b's campaign S2 arena): the coordinate-0 trampolines at sign words
1700..1725 (six chain constants `lui t2,16; addi t2,t2,128+4i`, two `lui t2,16; or t1,t1,t2; ori t1,t1,1537`). -/
def arenaCode : List (BitVec 32) := ((SigGolfCandidate.T3M.Images.signReferenceCode_6).drop 164).take 26
def signNew : List (BitVec 32) := headCode ++ (coordCode0 ++ (coordCode1 ++ (coordCode2 ++ (coordCode3 ++ (coordCode4 ++ (coordCode5 ++ (coordCode6 ++ (coordCode7 ++ (coordCode8 ++ tailCode)))))))))
def leafIdx : List Nat := [11201,12252,13312,14372,15431,16491,17551,18610,19670]
def qIdx : List Nat := [11201,11349,11494,11639,11784,11929,12252,12407,12552,12697,12842,12987,13312,13467,13612,13757,13902,14047,14372,14527,14672,14817,14962,15107,15431,15586,15731,15876,16021,16166,16491,16646,16791,16936,17081,17226,17551,17706,17851,17996,18141,18286,18610,18765,18910,19055,19200,19345,19670,19825,19970,20115,20260,20405]
def chkIdx : List Nat := [11246,11267,11288,11309,11330,11391,11412,11433,11454,11475,11536,11557,11578,11599,11620,11681,11702,11723,11744,11765,11826,11847,11868,11889,11910,11971,11992,12013,12034,12055,12304,12325,12346,12367,12388,12449,12470,12491,12512,12533,12594,12615,12636,12657,12678,12739,12760,12781,12802,12823,12884,12905,12926,12947,12968,13029,13050,13071,13092,13113,13364,13385,13406,13427,13448,13509,13530,13551,13572,13593,13654,13675,13696,13717,13738,13799,13820,13841,13862,13883,13944,13965,13986,14007,14028,14089,14110,14131,14152,14173,14424,14445,14466,14487,14508,14569,14590,14611,14632,14653,14714,14735,14756,14777,14798,14859,14880,14901,14922,14943,15004,15025,15046,15067,15088,15149,15170,15191,15212,15233,15483,15504,15525,15546,15567,15628,15649,15670,15691,15712,15773,15794,15815,15836,15857,15918,15939,15960,15981,16002,16063,16084,16105,16126,16147,16208,16229,16250,16271,16292,16543,16564,16585,16606,16627,16688,16709,16730,16751,16772,16833,16854,16875,16896,16917,16978,16999,17020,17041,17062,17123,17144,17165,17186,17207,17268,17289,17310,17331,17352,17603,17624,17645,17666,17687,17748,17769,17790,17811,17832,17893,17914,17935,17956,17977,18038,18059,18080,18101,18122,18183,18204,18225,18246,18267,18328,18349,18370,18391,18412,18662,18683,18704,18725,18746,18807,18828,18849,18870,18891,18952,18973,18994,19015,19036,19097,19118,19139,19160,19181,19242,19263,19284,19305,19326,19387,19408,19429,19450,19471,19722,19743,19764,19785,19806,19867,19888,19909,19930,19951,20012,20033,20054,20075,20096,20157,20178,20199,20220,20241,20302,20323,20344,20365,20386,20447,20468,20489,20510,20531]
def skipIdx : List Nat := [11257,11278,11299,11320,11341,11402,11423,11444,11465,11486,11547,11568,11589,11610,11631,11692,11713,11734,11755,11776,11837,11858,11879,11900,11921,11982,12003,12024,12045,12066,12315,12336,12357,12378,12399,12460,12481,12502,12523,12544,12605,12626,12647,12668,12689,12750,12771,12792,12813,12834,12895,12916,12937,12958,12979,13040,13061,13082,13103,13124,13375,13396,13417,13438,13459,13520,13541,13562,13583,13604,13665,13686,13707,13728,13749,13810,13831,13852,13873,13894,13955,13976,13997,14018,14039,14100,14121,14142,14163,14184,14435,14456,14477,14498,14519,14580,14601,14622,14643,14664,14725,14746,14767,14788,14809,14870,14891,14912,14933,14954,15015,15036,15057,15078,15099,15160,15181,15202,15223,15244,15494,15515,15536,15557,15578,15639,15660,15681,15702,15723,15784,15805,15826,15847,15868,15929,15950,15971,15992,16013,16074,16095,16116,16137,16158,16219,16240,16261,16282,16303,16554,16575,16596,16617,16638,16699,16720,16741,16762,16783,16844,16865,16886,16907,16928,16989,17010,17031,17052,17073,17134,17155,17176,17197,17218,17279,17300,17321,17342,17363,17614,17635,17656,17677,17698,17759,17780,17801,17822,17843,17904,17925,17946,17967,17988,18049,18070,18091,18112,18133,18194,18215,18236,18257,18278,18339,18360,18381,18402,18423,18673,18694,18715,18736,18757,18818,18839,18860,18881,18902,18963,18984,19005,19026,19047,19108,19129,19150,19171,19192,19253,19274,19295,19316,19337,19398,19419,19440,19461,19482,19733,19754,19775,19796,19817,19878,19899,19920,19941,19962,20023,20044,20065,20086,20107,20168,20189,20210,20231,20252,20313,20334,20355,20376,20397,20458,20479,20500,20521,20542]
def lIdx : List Nat := [12074,13132,14192,15252,16311,17371,18431,19490,20550]
def tIdx : List Nat := [12092,13151,14211,15271,16330,17390,18450,19509,20569]
def nodeIdx : List Nat := [12096,13155,14215,15275,16334,17394,18454,19513,20573]
def ntIdx : List Nat := [12122,13181,14241,15301,16360,17420,18480,19539,20599]
def rIdx : List Nat := [12135,13194,14254,15314,16373,17433,18493,19552,20612]
def lwuIdx : List Nat := [11199,12250,13310,14370,15429,16489,17549,18608,19668]
def sfIdx : List Nat := [11030,11045,11059,11074,11089,11103,11118,11133,11147,11162]
def scIdx : List Nat := [11039,11053,11068,11083,11097,11112,11127,11141,11156]
def costBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.signPrefix_0, SigGolfCandidate.T3M.Images.signPrefix_1, SigGolfCandidate.T3M.Images.signPrefix_2, SigGolfCandidate.T3M.Images.signPrefix_3, SigGolfCandidate.T3M.Images.signPrefix_4, SigGolfCandidate.T3M.Images.signPrefix_5, SigGolfCandidate.T3M.Images.signPrefix_6, SigGolfCandidate.T3M.Images.signPrefix_7, SigGolfCandidate.T3M.Images.signPrefix_8, SigGolfCandidate.T3M.Images.signPrefix_9, SigGolfCandidate.T3M.Images.signPrefix_10, SigGolfCandidate.T3M.Images.signPrefix_11, SigGolfCandidate.T3M.Images.signPrefix_12, SigGolfCandidate.T3M.Images.signPrefix_13, SigGolfCandidate.T3M.Images.signPrefix_14, SigGolfCandidate.T3M.Images.signPrefix_15, SigGolfCandidate.T3M.Images.signPrefix_16, SigGolfCandidate.T3M.Images.signPrefix_17, SigGolfCandidate.T3M.Images.signPrefix_18, SigGolfCandidate.T3M.Images.signPrefix_19, SigGolfCandidate.T3M.Images.signPrefix_20, SigGolfCandidate.T3M.Images.signPrefix_21, SigGolfCandidate.T3M.Images.signPrefix_22, SigGolfCandidate.T3M.Images.signPrefix_23, SigGolfCandidate.T3M.Images.signPrefix_24, SigGolfCandidate.T3M.Images.signPrefix_25, SigGolfCandidate.T3M.Images.signPrefix_26, SigGolfCandidate.T3M.Images.signPrefix_27, SigGolfCandidate.T3M.Images.signPrefix_28, SigGolfCandidate.T3M.Images.signPrefix_29, SigGolfCandidate.T3M.Images.signPrefix_30, SigGolfCandidate.T3M.Images.signPrefix_31, SigGolfCandidate.T3M.Images.signPrefix_32, SigGolfCandidate.T3M.Images.signPrefix_33, SigGolfCandidate.T3M.Images.signPrefix_34, SigGolfCandidate.T3M.Images.signPrefix_35, SigGolfCandidate.T3M.Images.signPrefix_36, SigGolfCandidate.T3M.Images.signPrefix_37, SigGolfCandidate.T3M.Images.signPrefix_38, SigGolfCandidate.T3M.Images.signPrefix_39, SigGolfCandidate.T3M.Images.signPrefix_40, SigGolfCandidate.T3M.Images.signPrefix_41, SigGolfCandidate.T3M.Images.signPrefix_42, SigGolfCandidate.T3M.Images.signPrefix_43, SigGolfCandidate.T3M.Images.signPrefix_44, SigGolfCandidate.T3M.Images.signPrefix_45, SigGolfCandidate.T3M.Images.signPrefix_46, SigGolfCandidate.T3M.Images.signPrefix_47, SigGolfCandidate.T3M.Images.signPrefix_48, SigGolfCandidate.T3M.Images.signPrefix_49, SigGolfCandidate.T3M.Images.signPrefix_50, SigGolfCandidate.T3M.Images.signPrefix_51, SigGolfCandidate.T3M.Images.signPrefix_52, SigGolfCandidate.T3M.Images.signPrefix_53, SigGolfCandidate.T3M.Images.signPrefix_54, SigGolfCandidate.T3M.Images.signPrefix_55, SigGolfCandidate.T3M.Images.signPrefix_56, SigGolfCandidate.T3M.Images.signPrefix_57, SigGolfCandidate.T3M.Images.signPrefix_58, SigGolfCandidate.T3M.Images.signPrefix_59, SigGolfCandidate.T3M.Images.signPrefix_60, SigGolfCandidate.T3M.Images.signPrefix_61, SigGolfCandidate.T3M.Images.signPrefix_62, SigGolfCandidate.T3M.Images.signPrefix_63].flatten
def tblBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.signPrefix_64, SigGolfCandidate.T3M.Images.signPrefix_65, SigGolfCandidate.T3M.Images.signPrefix_66, SigGolfCandidate.T3M.Images.signPrefix_67, SigGolfCandidate.T3M.Images.signPrefix_68, SigGolfCandidate.T3M.Images.signPrefix_69, SigGolfCandidate.T3M.Images.signPrefix_70, SigGolfCandidate.T3M.Images.signPrefix_71, SigGolfCandidate.T3M.Images.signPrefix_72, SigGolfCandidate.T3M.Images.signPrefix_73, SigGolfCandidate.T3M.Images.signPrefix_74, SigGolfCandidate.T3M.Images.signPrefix_75, SigGolfCandidate.T3M.Images.signPrefix_76, SigGolfCandidate.T3M.Images.signPrefix_77, SigGolfCandidate.T3M.Images.signPrefix_78, SigGolfCandidate.T3M.Images.signPrefix_79, SigGolfCandidate.T3M.Images.signPrefix_80, SigGolfCandidate.T3M.Images.signPrefix_81, SigGolfCandidate.T3M.Images.signPrefix_82, SigGolfCandidate.T3M.Images.signPrefix_83, SigGolfCandidate.T3M.Images.signPrefix_84, SigGolfCandidate.T3M.Images.signPrefix_85, SigGolfCandidate.T3M.Images.signPrefix_86, SigGolfCandidate.T3M.Images.signPrefix_87, SigGolfCandidate.T3M.Images.signPrefix_88, SigGolfCandidate.T3M.Images.signPrefix_89, SigGolfCandidate.T3M.Images.signPrefix_90, SigGolfCandidate.T3M.Images.signPrefix_91, SigGolfCandidate.T3M.Images.signPrefix_92, SigGolfCandidate.T3M.Images.signPrefix_93, SigGolfCandidate.T3M.Images.signPrefix_94, SigGolfCandidate.T3M.Images.signPrefix_95, SigGolfCandidate.T3M.Images.signPrefix_96, SigGolfCandidate.T3M.Images.signPrefix_97, SigGolfCandidate.T3M.Images.signPrefix_98, SigGolfCandidate.T3M.Images.signPrefix_99, SigGolfCandidate.T3M.Images.signPrefix_100, SigGolfCandidate.T3M.Images.signPrefix_101, SigGolfCandidate.T3M.Images.signPrefix_102, SigGolfCandidate.T3M.Images.signPrefix_103, SigGolfCandidate.T3M.Images.signPrefix_104, SigGolfCandidate.T3M.Images.signPrefix_105, SigGolfCandidate.T3M.Images.signPrefix_106, SigGolfCandidate.T3M.Images.signPrefix_107, SigGolfCandidate.T3M.Images.signPrefix_108, SigGolfCandidate.T3M.Images.signPrefix_109, SigGolfCandidate.T3M.Images.signPrefix_110, SigGolfCandidate.T3M.Images.signPrefix_111, SigGolfCandidate.T3M.Images.signPrefix_112, SigGolfCandidate.T3M.Images.signPrefix_113, SigGolfCandidate.T3M.Images.signPrefix_114, SigGolfCandidate.T3M.Images.signPrefix_115, SigGolfCandidate.T3M.Images.signPrefix_116, SigGolfCandidate.T3M.Images.signPrefix_117, SigGolfCandidate.T3M.Images.signPrefix_118, SigGolfCandidate.T3M.Images.signPrefix_119, SigGolfCandidate.T3M.Images.signPrefix_120, SigGolfCandidate.T3M.Images.signPrefix_121, SigGolfCandidate.T3M.Images.signPrefix_122, SigGolfCandidate.T3M.Images.signPrefix_123, SigGolfCandidate.T3M.Images.signPrefix_124, SigGolfCandidate.T3M.Images.signPrefix_125, SigGolfCandidate.T3M.Images.signPrefix_126, SigGolfCandidate.T3M.Images.signPrefix_127, SigGolfCandidate.T3M.Images.signPrefix_128, SigGolfCandidate.T3M.Images.signPrefix_129, SigGolfCandidate.T3M.Images.signPrefix_130, SigGolfCandidate.T3M.Images.signPrefix_131, SigGolfCandidate.T3M.Images.signPrefix_132, SigGolfCandidate.T3M.Images.signPrefix_133, SigGolfCandidate.T3M.Images.signPrefix_134, SigGolfCandidate.T3M.Images.signPrefix_135, SigGolfCandidate.T3M.Images.signPrefix_136, SigGolfCandidate.T3M.Images.signPrefix_137, SigGolfCandidate.T3M.Images.signPrefix_138, SigGolfCandidate.T3M.Images.signPrefix_139, SigGolfCandidate.T3M.Images.signPrefix_140, SigGolfCandidate.T3M.Images.signPrefix_141, SigGolfCandidate.T3M.Images.signPrefix_142, SigGolfCandidate.T3M.Images.signPrefix_143, SigGolfCandidate.T3M.Images.signPrefix_144, SigGolfCandidate.T3M.Images.signPrefix_145, SigGolfCandidate.T3M.Images.signPrefix_146, SigGolfCandidate.T3M.Images.signPrefix_147, SigGolfCandidate.T3M.Images.signPrefix_148, SigGolfCandidate.T3M.Images.signPrefix_149, SigGolfCandidate.T3M.Images.signPrefix_150, SigGolfCandidate.T3M.Images.signPrefix_151, SigGolfCandidate.T3M.Images.signPrefix_152, SigGolfCandidate.T3M.Images.signPrefix_153, SigGolfCandidate.T3M.Images.signPrefix_154, SigGolfCandidate.T3M.Images.signPrefix_155, SigGolfCandidate.T3M.Images.signPrefix_156, SigGolfCandidate.T3M.Images.signPrefix_157, SigGolfCandidate.T3M.Images.signPrefix_158, SigGolfCandidate.T3M.Images.signPrefix_159, SigGolfCandidate.T3M.Images.signPrefix_160, SigGolfCandidate.T3M.Images.signPrefix_161, SigGolfCandidate.T3M.Images.signPrefix_162, SigGolfCandidate.T3M.Images.signPrefix_163, SigGolfCandidate.T3M.Images.signPrefix_164, SigGolfCandidate.T3M.Images.signPrefix_165, SigGolfCandidate.T3M.Images.signPrefix_166, SigGolfCandidate.T3M.Images.signPrefix_167, SigGolfCandidate.T3M.Images.signPrefix_168, SigGolfCandidate.T3M.Images.signPrefix_169, SigGolfCandidate.T3M.Images.signPrefix_170, SigGolfCandidate.T3M.Images.signPrefix_171, SigGolfCandidate.T3M.Images.signPrefix_172, SigGolfCandidate.T3M.Images.signPrefix_173, SigGolfCandidate.T3M.Images.signPrefix_174, SigGolfCandidate.T3M.Images.signPrefix_175, SigGolfCandidate.T3M.Images.signPrefix_176, SigGolfCandidate.T3M.Images.signPrefix_177, SigGolfCandidate.T3M.Images.signPrefix_178, SigGolfCandidate.T3M.Images.signPrefix_179, SigGolfCandidate.T3M.Images.signPrefix_180, SigGolfCandidate.T3M.Images.signPrefix_181, SigGolfCandidate.T3M.Images.signPrefix_182, SigGolfCandidate.T3M.Images.signPrefix_183, SigGolfCandidate.T3M.Images.signPrefix_184, SigGolfCandidate.T3M.Images.signPrefix_185, SigGolfCandidate.T3M.Images.signPrefix_186, SigGolfCandidate.T3M.Images.signPrefix_187, SigGolfCandidate.T3M.Images.signPrefix_188, SigGolfCandidate.T3M.Images.signPrefix_189, SigGolfCandidate.T3M.Images.signPrefix_190, SigGolfCandidate.T3M.Images.signPrefix_191, SigGolfCandidate.T3M.Images.signPrefix_192, SigGolfCandidate.T3M.Images.signPrefix_193, SigGolfCandidate.T3M.Images.signPrefix_194, SigGolfCandidate.T3M.Images.signPrefix_195, SigGolfCandidate.T3M.Images.signPrefix_196, SigGolfCandidate.T3M.Images.signPrefix_197, SigGolfCandidate.T3M.Images.signPrefix_198, SigGolfCandidate.T3M.Images.signPrefix_199, SigGolfCandidate.T3M.Images.signPrefix_200, SigGolfCandidate.T3M.Images.signPrefix_201, SigGolfCandidate.T3M.Images.signPrefix_202, SigGolfCandidate.T3M.Images.signPrefix_203, SigGolfCandidate.T3M.Images.signPrefix_204, SigGolfCandidate.T3M.Images.signPrefix_205, SigGolfCandidate.T3M.Images.signPrefix_206, SigGolfCandidate.T3M.Images.signPrefix_207, SigGolfCandidate.T3M.Images.signPrefix_208, SigGolfCandidate.T3M.Images.signPrefix_209, SigGolfCandidate.T3M.Images.signPrefix_210, SigGolfCandidate.T3M.Images.signPrefix_211, SigGolfCandidate.T3M.Images.signPrefix_212, SigGolfCandidate.T3M.Images.signPrefix_213, SigGolfCandidate.T3M.Images.signPrefix_214, SigGolfCandidate.T3M.Images.signPrefix_215, SigGolfCandidate.T3M.Images.signPrefix_216, SigGolfCandidate.T3M.Images.signPrefix_217, SigGolfCandidate.T3M.Images.signPrefix_218, SigGolfCandidate.T3M.Images.signPrefix_219, SigGolfCandidate.T3M.Images.signPrefix_220, SigGolfCandidate.T3M.Images.signPrefix_221, SigGolfCandidate.T3M.Images.signPrefix_222, SigGolfCandidate.T3M.Images.signPrefix_223, SigGolfCandidate.T3M.Images.signPrefix_224, SigGolfCandidate.T3M.Images.signPrefix_225, SigGolfCandidate.T3M.Images.signPrefix_226, SigGolfCandidate.T3M.Images.signPrefix_227, SigGolfCandidate.T3M.Images.signPrefix_228, SigGolfCandidate.T3M.Images.signPrefix_229, SigGolfCandidate.T3M.Images.signPrefix_230, SigGolfCandidate.T3M.Images.signPrefix_231, SigGolfCandidate.T3M.Images.signPrefix_232, SigGolfCandidate.T3M.Images.signPrefix_233, SigGolfCandidate.T3M.Images.signPrefix_234, SigGolfCandidate.T3M.Images.signPrefix_235, SigGolfCandidate.T3M.Images.signPrefix_236, SigGolfCandidate.T3M.Images.signPrefix_237, SigGolfCandidate.T3M.Images.signPrefix_238, SigGolfCandidate.T3M.Images.signPrefix_239, SigGolfCandidate.T3M.Images.signPrefix_240, SigGolfCandidate.T3M.Images.signPrefix_241, SigGolfCandidate.T3M.Images.signPrefix_242, SigGolfCandidate.T3M.Images.signPrefix_243, SigGolfCandidate.T3M.Images.signPrefix_244, SigGolfCandidate.T3M.Images.signPrefix_245, SigGolfCandidate.T3M.Images.signPrefix_246, SigGolfCandidate.T3M.Images.signPrefix_247, SigGolfCandidate.T3M.Images.signPrefix_248, SigGolfCandidate.T3M.Images.signPrefix_249, SigGolfCandidate.T3M.Images.signPrefix_250, SigGolfCandidate.T3M.Images.signPrefix_251, SigGolfCandidate.T3M.Images.signPrefix_252, SigGolfCandidate.T3M.Images.signPrefix_253, SigGolfCandidate.T3M.Images.signPrefix_254, SigGolfCandidate.T3M.Images.signPrefix_255, SigGolfCandidate.T3M.Images.signPrefix_256, SigGolfCandidate.T3M.Images.signPrefix_257, SigGolfCandidate.T3M.Images.signPrefix_258, SigGolfCandidate.T3M.Images.signPrefix_259, SigGolfCandidate.T3M.Images.signPrefix_260, SigGolfCandidate.T3M.Images.signPrefix_261, SigGolfCandidate.T3M.Images.signPrefix_262, SigGolfCandidate.T3M.Images.signPrefix_263, SigGolfCandidate.T3M.Images.signPrefix_264, SigGolfCandidate.T3M.Images.signPrefix_265, SigGolfCandidate.T3M.Images.signPrefix_266, SigGolfCandidate.T3M.Images.signPrefix_267, SigGolfCandidate.T3M.Images.signPrefix_268, SigGolfCandidate.T3M.Images.signPrefix_269, SigGolfCandidate.T3M.Images.signPrefix_270, SigGolfCandidate.T3M.Images.signPrefix_271, SigGolfCandidate.T3M.Images.signPrefix_272, SigGolfCandidate.T3M.Images.signPrefix_273, SigGolfCandidate.T3M.Images.signPrefix_274, SigGolfCandidate.T3M.Images.signPrefix_275, SigGolfCandidate.T3M.Images.signPrefix_276, SigGolfCandidate.T3M.Images.signPrefix_277, SigGolfCandidate.T3M.Images.signPrefix_278, SigGolfCandidate.T3M.Images.signPrefix_279, SigGolfCandidate.T3M.Images.signPrefix_280, SigGolfCandidate.T3M.Images.signPrefix_281, SigGolfCandidate.T3M.Images.signPrefix_282, SigGolfCandidate.T3M.Images.signPrefix_283, SigGolfCandidate.T3M.Images.signPrefix_284, SigGolfCandidate.T3M.Images.signPrefix_285, SigGolfCandidate.T3M.Images.signPrefix_286, SigGolfCandidate.T3M.Images.signPrefix_287, SigGolfCandidate.T3M.Images.signPrefix_288, SigGolfCandidate.T3M.Images.signPrefix_289, SigGolfCandidate.T3M.Images.signPrefix_290, SigGolfCandidate.T3M.Images.signPrefix_291, SigGolfCandidate.T3M.Images.signPrefix_292, SigGolfCandidate.T3M.Images.signPrefix_293, SigGolfCandidate.T3M.Images.signPrefix_294, SigGolfCandidate.T3M.Images.signPrefix_295, SigGolfCandidate.T3M.Images.signPrefix_296, SigGolfCandidate.T3M.Images.signPrefix_297, SigGolfCandidate.T3M.Images.signPrefix_298, SigGolfCandidate.T3M.Images.signPrefix_299, SigGolfCandidate.T3M.Images.signPrefix_300, SigGolfCandidate.T3M.Images.signPrefix_301, SigGolfCandidate.T3M.Images.signPrefix_302, SigGolfCandidate.T3M.Images.signPrefix_303, SigGolfCandidate.T3M.Images.signPrefix_304, SigGolfCandidate.T3M.Images.signPrefix_305, SigGolfCandidate.T3M.Images.signPrefix_306, SigGolfCandidate.T3M.Images.signPrefix_307, SigGolfCandidate.T3M.Images.signPrefix_308, SigGolfCandidate.T3M.Images.signPrefix_309, SigGolfCandidate.T3M.Images.signPrefix_310, SigGolfCandidate.T3M.Images.signPrefix_311, SigGolfCandidate.T3M.Images.signPrefix_312, SigGolfCandidate.T3M.Images.signPrefix_313, SigGolfCandidate.T3M.Images.signPrefix_314, SigGolfCandidate.T3M.Images.signPrefix_315, SigGolfCandidate.T3M.Images.signPrefix_316, SigGolfCandidate.T3M.Images.signPrefix_317, SigGolfCandidate.T3M.Images.signPrefix_318, SigGolfCandidate.T3M.Images.signPrefix_319].flatten
end ClaudeWCT.W9.Machine.Sign
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_Common ====
section

section





namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M Pieces Layer chainCount height privateMac privateNonce)
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev FOUT : Nat := 0x203A0
abbrev IDXV : Nat := 0x20550
abbrev TBL : Nat := 0xfef000
abbrev COST : Nat := 0xfeb000
abbrev PRIVW : Nat := 0x50000
abbrev PAIRW : Nat := 0x50040
abbrev CHAINW : Nat := 0x50100
abbrev LEAFW : Nat := 0x50200
abbrev NODEW : Nat := 0x50300
abbrev FORW : Nat := 0x50600
abbrev NOUTW : Nat := 0x50500
abbrev HEAPW : Nat := 0x51000
abbrev SCREND : Nat := 0x52010
abbrev COEF : Nat := 0x50800
def hook153 : BitVec 32 := 0x1890a06f
def hook540 : BitVec 32 := 0x3791306f
/-- The sign code: the record window at 11003, (nested FTS r1-1) the trampolines at 21450 and (C4, FTS
coordinate + 1) the coordinate-0 arena at 1700. -/
def NewCodeAt (im : Image) : Prop :=
  signNew <+: im.code.drop 11003 ∧ signTramp <+: im.code.drop 21450 ∧ arenaCode <+: im.code.drop 1700
/-- [h2 lane] the sign prepass appended at word 20813 (entered from the record's copy at 20730): move digest 192 (the top
sibling, scratch 0x7ca0) to the last scratch slot and digests 193..340 down one slot, then return to 20731. -/
def h2SignTail : List (BitVec 32) := [0x8e37, 0xca0e0e13, 0xe3703, 0x8e3783, 0xe0e93, 0x10e0e13, 0x8f37, 0x5f0f0f13,
  0xe3303, 0x8e3383, 0x6eb023, 0x7eb423, 0x10e0e13, 0x10e8e93, 0xffee64e3, 0xeeb023, 0xfeb423, 0x8e37, 0xe71ff06f]
def HooksAt (im : Image) : Prop :=
  im.code[153]? = some hook153 ∧ im.code[540]? = some hook540 ∧ im.code[545]? = some 0x00000073 ∧
    h2SignTail <+: im.code.drop 20813
def SignCodeAt (im : Image) : Prop := NewCodeAt im ∧ HooksAt im
def TableAt (t : MachineState) : Prop :=
  ∀ k < 8192, t.getMem (BitVec.ofNat 64 (TBL + 8 * k)) = bytesToWordLE ((tblBytes.drop (8 * k)).take 8)
def CostAt (t : MachineState) : Prop :=
  ∀ k < 2048, t.getMem (BitVec.ofNat 64 (COST + 8 * k)) = bytesToWordLE ((costBytes.drop (8 * k)).take 8)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
structure SearchPre (rho : Digest) (m : Message) (s : MachineState) : Prop where
  pc : s.pc = pcOf 153
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
  cost : CostAt s
structure FailedS (t : MachineState) : Prop where
  pc : t.pc = pcOf 11174
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
def searchRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x22, .x24, .x25, .x28]
def SearchW (A : Nat) : Prop := A = DIG + 16 ∨ A = DIG + 24 ∨ (NBUF ≤ A ∧ A < NBUF + 32) ∨ A = IDXV
def SearchPost (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedS t
  | some (c, N), t => t.pc = pcOf 11175 ∧ t.getReg .x5 = 0 ∧ WCT9.producerAdmissible N = true ∧ OutAt t NBUF N ∧
      t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex N) ∧
      c.toNat < WCT9.digestAttemptLimit ∧ RegsExcept s t searchRegs ∧ Frame s t SearchW
def trialC : Nat := 200
def searchC : Nat := WCT9.digestAttemptLimit * trialC + 200
def SearchGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ (sk : BitVec 256) (rho : Digest) (m : Message) (s : MachineState),
    SearchPre rho m s →
      TBSim im sk s searchC (WCT9.digestSearch rho m 0 WCT9.digestAttemptLimit) (SearchPost s)
def ScrZero (A : Nat) : Prop :=
  A = PRIVW + 48 ∨ A = PRIVW + 56 ∨ A = CHAINW ∨ A = CHAINW + 8 ∨ A = CHAINW + 32 ∨ A = CHAINW + 40 ∨
    A = NODEW + 32 ∨ A = NODEW + 40
structure FtsPre (sk : BitVec 256) (N : HashOutput) (s : MachineState) : Prop where
  pc : s.pc = pcOf 11175
  x5 : s.getReg .x5 = 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex N)
  adm : WCT9.admissible N = true
  nbuf : OutAt s NBUF N
  sk : ∀ k < 4, s.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → s.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt s
def ftsRegs : List Reg := [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x24, .x25, .x26, .x28,
  .x29]
/-- Nested FTS (r1-1): `0x20290..0x202a0` is the L3 encoding R slot, which now receives `R8`. -/
def FtsW (A : Nat) : Prop := (PRIVW ≤ A ∧ A < SCREND) ∨ (SIG + 16 ≤ A ∧ A < SIG + 1888) ∨ (FOUT ≤ A ∧ A < FOUT + 32) ∨
  (0x20290 ≤ A ∧ A < 0x20290 + 16)
def OpeningAt (t : MachineState) (k : Nat) (op : WCT9.Opening) : Prop :=
  (∀ i : Fin 6, DigAt t (SIG + 16 + 208 * k + 16 * i.val) (op.values i)) ∧
    ∀ l : Fin 7, DigAt t (SIG + 112 + 208 * k + 16 * l.val) (op.path l)
/-- Nested FTS (r1-1): the FTS part ends with the last top pair `(L8, R8)` at `FOUT` (L3 message) and `0x20290`
(the encoding R slot). -/
def FtsPost (s : MachineState) : List WCT9.Opening × (Digest × Digest) → MachineState → Prop
  | (ops, top), t => t.pc = pcOf 370 ∧ t.getReg .x5 = 0 ∧ DigAt t FOUT top.1 ∧ DigAt t 0x20290 top.2 ∧ ops.length = 9 ∧
      (∀ k < 9, OpeningAt t k (ops.getD k ⟨fun _ => 0, fun _ => 0⟩)) ∧ RegsExcept s t ftsRegs ∧ Frame s t FtsW
def ftsC : Nat := 114000000
def FtsGood (im : Image) : Prop :=
  NewCodeAt im → ∀ (sk : BitVec 256) (N : HashOutput) (s : MachineState), FtsPre sk N s →
    TBSim im sk s ftsC (WCT9.signForest (WCT9.digestIndex N) N) (FtsPost s)
/-- H2: scratch slot (relative to digest 127) read for compact output slot `p`: digest 192 (the top sibling,
slot 65) goes last, digests 193..340 move down one slot. -/
def cpIdx (p : Nat) : Nat := if p < 65 then p else if p < 213 then p + 1 else 65
def CompactPost (s t : MachineState) : Prop :=
  t.pc = pcOf 20745 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
    (∀ k < 428, t.getMem (BitVec.ofNat 64 (SIG + 1888 + 8 * k)) =
      s.getMem (BitVec.ofNat 64 (SIG + 2192 + 16 * cpIdx (k / 2) + 8 * (k % 2)))) ∧
    Frame s t (fun A => SIG + 1888 ≤ A ∧ A < SIG + 5616)
def compactK : Nat := 1 + 9 + 148 * 7 + 4 + 5 + 214 * 7 + 2
def CompactGood (im : Image) : Prop :=
  NewCodeAt im → HooksAt im → ∀ s : MachineState, s.pc = pcOf 540 →
    ∃ t, Steps im s compactK compactK t ∧ CompactPost s t
structure FailedT (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
structure HookPre (sk : BitVec 256) (m : Message) (rho : Digest) (t : MachineState) : Prop where
  search : SearchPre rho m t
  sigRho : DigAt t SIG rho
  sk : ∀ k < 4, t.getMem (BitVec.ofNat 64 (SK + 8 * k)) = sk.extractLsb' (64 * k) 64
  zero : ∀ A, ScrZero A → t.getMem (BitVec.ofNat 64 A) = 0
  table : TableAt t
def frontC : Nat := 2490014
def FrontSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (m : Message) (s0 : MachineState)
    (Inv : MachineState → Prop) : Prop :=
  ∀ {α : Type} (W : Nat) (Q : Option α → MachineState → Prop) (K : Digest → M (Option α)),
    (∀ t, FailedT t → Q none t) →
    (∀ rho t, HookPre sk m rho t → Inv t → TBSim im sk t W (K rho) Q) →
    TBSim im sk s0 (frontC + W) (do
      let tag ← privateMac (cacheDec cache).region
      if tag ≠ (cacheDec cache).tag then pure none else privateNonce m >>= K) Q
structure LayPre (index : Nat) (top : Digest × Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 370
  x5 : t.getReg .x5 = 0
  hidx : index < 2 ^ 31
  idx : t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index
  root : DigAt t FOUT top.1
  right : DigAt t 0x20290 top.2
def t3LayIdx (lay : Layer) : Nat := (![137, 203, 253, 302] : Layer → Nat) lay
def PieceAt (u : MachineState) (lay : Layer) (p : Pieces) : Prop :=
  (∀ i < chainCount lay, DigAt u (SIG + 16 * (t3LayIdx lay + i)) (p.1.getD i 0)) ∧
    ∀ j < height lay, DigAt u (SIG + 16 * (t3LayIdx lay + chainCount lay + j)) (p.2.getD j 0)
def LayPost (t : MachineState) : Option (List Pieces) → MachineState → Prop
  | none, u => FailedT u
  | some ps, u => u.pc = pcOf 540 ∧ ps.length = 4 ∧ (∀ lay : Layer, PieceAt u lay (ps.getD lay.val ([], []))) ∧
      Frame t u (fun A => ¬ (SIG ≤ A ∧ A < SIG + 2192))
def layC : Nat := 3575044093
def LayersSpec (im : Image) (sk : BitVec 256) (cache : Bytes 131072) (Inv : MachineState → Prop) : Prop :=
  ∀ (index : Nat) (top : Digest × Digest) (t : MachineState), LayPre index top t → Inv t →
    TBSim im sk t layC (WCT9.signLayersBC (cacheDec cache) index 4 (.pair top.1 top.2)) (LayPost t)
def newRegs : List Reg := [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x19, .x20, .x21, .x22,
  .x24, .x25, .x26, .x28, .x29]
def NewW (A : Nat) : Prop := SearchW A ∨ FtsW A
def InvStable (Inv : MachineState → Prop) : Prop :=
  ∀ t u, Inv t → Frame t u NewW → RegsExcept t u newRegs → Inv u
def wsub (imgs : Phase → Image) : Submission :=
  ⟨⟨5310, 24828, 131072⟩, ⟨0x6620, 0x80, 0xa0, 0x80000, 0x7000, 0x520⟩, imgs⟩
structure Unchanged (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop) :
    Prop where
  front : ∀ sk cache m, ∃ s0, initialState (wsub imgs) .sign (sk, cache, m) = some s0 ∧
    FrontSpec (imgs .sign) sk cache m s0 (Inv sk cache m)
  stable : ∀ sk cache m, InvStable (Inv sk cache m)
  layers : ∀ sk cache m, LayersSpec (imgs .sign) sk cache (Inv sk cache m)
def SignRefinesW (imgs : Phase → Image) : Prop :=
  ∀ (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> (wsub imgs).run .sign (sk, cache, m) =
      (fun p => (p.1.map W9.T3M.sigBC, p.2.1, p.2.2)) <$> countBoth (mrealize sk (WCT9.Rev3.sign (cacheDec cache) m))
def SignTerminatesW (imgs : Phase → Image) : Prop :=
  ∀ (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (m : Message),
    ((wsub imgs).runWith hash .sign (sk, cache, m)).finished = true ∧
      ((wsub imgs).runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT
def SignMain : Prop :=
  ∀ (imgs : Phase → Image) (Inv : BitVec 256 → Bytes 131072 → Message → MachineState → Prop),
    SignCodeAt (imgs .sign) → Unchanged imgs Inv → SignRefinesW imgs ∧ SignTerminatesW imgs
end ClaudeWCT.W9.Machine.Sign
end

section

section
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
def scfg : Config := {}
def cbase (c : Nat) : Nat := fieldIdx.getD c 0
def headLook (n : Nat) : Option (BitVec 32) := if 11003 ≤ n then headCode[n - 11003]? else none
/-- Nested FTS (r1-1): the trampolines at 21450..21666. -/
def trampLook (n : Nat) : Option (BitVec 32) := if 21450 ≤ n then signTramp[n - 21450]? else none
/-- C4: the coordinate-0 arena at 1700..1725 (below every coordinate window). -/
def arenaLook (n : Nat) : Option (BitVec 32) := if 1700 ≤ n then arenaCode[n - 1700]? else none
/-- A coordinate's code window, falling through to the trampolines (nested FTS r1-1), and below the window to the
C4 arena. -/
def coordLook (c n : Nat) : Option (BitVec 32) :=
  if cbase c ≤ n then
    (match (coordCodes.getD c [])[n - cbase c]? with | some w => some w | none => trampLook n)
  else arenaLook n
def tailLook (n : Nat) : Option (BitVec 32) := if 20715 ≤ n then tailCode[n - 20715]? else none
def hookLook (n : Nat) : Option (BitVec 32) :=
  if n = 153 then some hook153 else if n = 540 then some hook540 else if n = 545 then some 0x00000073 else none
def run (look : Nat → Option (BitVec 32)) (stops : List Nat) (n : Nat) (dirs : List Dir) : Option PRes :=
  pathAux scfg look (stops.map pcOf) 200 (pcOf n) dirs (σK []) []
theorem headCode_length : headCode.length = 183 := by decide +kernel
theorem coordCode0_length : coordCode0.length = 1052 := by decide +kernel
theorem coordCode1_length : coordCode1.length = 1059 := by decide +kernel
theorem coordCode2_length : coordCode2.length = 1060 := by decide +kernel
theorem coordCode3_length : coordCode3.length = 1060 := by decide +kernel
theorem coordCode4_length : coordCode4.length = 1059 := by decide +kernel
theorem coordCode5_length : coordCode5.length = 1060 := by decide +kernel
theorem coordCode6_length : coordCode6.length = 1060 := by decide +kernel
theorem coordCode7_length : coordCode7.length = 1059 := by decide +kernel
theorem coordCode8_length : coordCode8.length = 1060 := by decide +kernel
theorem tailCode_length : tailCode.length = 56 := by decide +kernel
theorem getElem?_append_off {α : Type} {a l : List α} {n k : Nat} {w : α} (ha : a.length = n)
    (h : l[k]? = some w) : (a ++ l)[n + k]? = some w := by
  rw [List.getElem?_append_right (by omega), ha, Nat.add_sub_cancel_left]; exact h
theorem getElem?_append_pre {α : Type} {a l : List α} {k : Nat} {w : α}
    (h : a[k]? = some w) : (a ++ l)[k]? = some w := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h
theorem signNew_head {k : Nat} {w : BitVec 32} (h : headCode[k]? = some w) : signNew[k]? = some w := by
  unfold signNew; exact getElem?_append_pre h
theorem signNew_tail {k : Nat} {w : BitVec 32} (h : tailCode[k]? = some w) : signNew[9712 + k]? = some w := by
  unfold signNew
  rw [show 9712 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (1059 + (1060 + (k)))))))))) by omega]
  exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_off coordCode7_length (getElem?_append_off coordCode8_length (h))))))))))
theorem signNew_coord {c k : Nat} (hc : c < 9) {w : BitVec 32} (h : (coordCodes.getD c [])[k]? = some w) :
    signNew[cbase c - 11003 + k]? = some w := by
  unfold signNew
  interval_cases c
  · rw [show cbase 0 - 11003 + k = 183 + (k) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_pre h)
  · rw [show cbase 1 - 11003 + k = 183 + (1052 + (k)) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_pre h))
  · rw [show cbase 2 - 11003 + k = 183 + (1052 + (1059 + (k))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_pre h)))
  · rw [show cbase 3 - 11003 + k = 183 + (1052 + (1059 + (1060 + (k)))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_pre h))))
  · rw [show cbase 4 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (k))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_pre h)))))
  · rw [show cbase 5 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (k)))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_pre h))))))
  · rw [show cbase 6 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (k))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_pre h)))))))
  · rw [show cbase 7 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (k)))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_pre h))))))))
  · rw [show cbase 8 - 11003 + k = 183 + (1052 + (1059 + (1060 + (1060 + (1059 + (1060 + (1060 + (1059 + (k))))))))) by simp [cbase, fieldIdx] <;> omega]
    exact getElem?_append_off headCode_length (getElem?_append_off coordCode0_length (getElem?_append_off coordCode1_length (getElem?_append_off coordCode2_length (getElem?_append_off coordCode3_length (getElem?_append_off coordCode4_length (getElem?_append_off coordCode5_length (getElem?_append_off coordCode6_length (getElem?_append_off coordCode7_length (getElem?_append_pre h)))))))))
theorem newCode_word {im : Image} (h : NewCodeAt im) {k : Nat} {w : BitVec 32} (hk : signNew[k]? = some w) :
    im.code[11003 + k]? = some w := by
  obtain ⟨rest, hrest⟩ := h.1
  have hlen : k < signNew.length := (List.getElem?_eq_some_iff.mp hk).1
  have h2 : (im.code.drop 11003)[k]? = some w := by
    rw [← hrest, List.getElem?_append_left hlen]; exact hk
  rwa [List.getElem?_drop] at h2
theorem headLook_ok {im : Image} (h : NewCodeAt im) : LookOK im headLook := by
  intro n w hw
  unfold headLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_head hw)
    rwa [Nat.add_sub_cancel' hle] at this
  · cases hw
theorem cbase_ge (c : Nat) (hc : c < 9) : 11003 ≤ cbase c := by
  interval_cases c <;> decide +kernel
theorem trampLook_ok {im : Image} (h : NewCodeAt im) : LookOK im trampLook := by
  intro n w hw
  obtain ⟨rest, hrest⟩ := h.2.1
  unfold trampLook at hw
  split at hw
  · rename_i hle
    have hlen : n - 21450 < signTramp.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop 21450)[n - 21450]? = some w := by
      rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, Nat.add_sub_cancel' hle] at h2
  · cases hw
theorem arenaLook_ok {im : Image} (h : NewCodeAt im) : LookOK im arenaLook := by
  intro n w hw
  obtain ⟨rest, hrest⟩ := h.2.2
  unfold arenaLook at hw
  split at hw
  · rename_i hle
    have hlen : n - 1700 < arenaCode.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop 1700)[n - 1700]? = some w := by
      rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, Nat.add_sub_cancel' hle] at h2
  · cases hw
theorem coordLook_ok {im : Image} (h : NewCodeAt im) {c : Nat} (hc : c < 9) : LookOK im (coordLook c) := by
  intro n w hw
  unfold coordLook at hw
  split at hw
  · rename_i hle
    split at hw
    · rename_i w' hw'
      cases hw
      have := newCode_word h (signNew_coord hc hw')
      have hb := cbase_ge c hc
      rwa [show 11003 + (cbase c - 11003 + (n - cbase c)) = n by omega] at this
    · exact trampLook_ok h n w hw
  · exact arenaLook_ok h n w hw
theorem tailLook_ok {im : Image} (h : NewCodeAt im) : LookOK im tailLook := by
  intro n w hw
  unfold tailLook at hw
  split at hw
  · rename_i hle
    have := newCode_word h (signNew_tail hw)
    rwa [show 11003 + (9712 + (n - 20715)) = n by omega] at this
  · cases hw
theorem hookLook_ok {im : Image} (h : HooksAt im) : LookOK im hookLook := by
  intro n w hw
  obtain ⟨h1, h2, h3, -⟩ := h
  unfold hookLook at hw
  split_ifs at hw with e1 e2 e3
  · subst e1; cases hw; exact h1
  · subst e2; cases hw; exact h2
  · subst e3; cases hw; exact h3
/-- The tail window falling through to the trampolines (nested FTS r1-1: the forest hash is replaced). -/
def forLook (n : Nat) : Option (BitVec 32) := match tailLook n with | some w => some w | none => trampLook n
theorem forLook_ok {im : Image} (h : NewCodeAt im) : LookOK im forLook := by
  intro n w hw
  unfold forLook at hw
  split at hw
  · rename_i w' hw'
    cases hw
    exact tailLook_ok h n _ hw'
  · exact trampLook_ok h n w hw
def h2Look (n : Nat) : Option (BitVec 32) := if 20813 ≤ n then h2SignTail[n - 20813]? else none
/-- The record's tail window, then the H2 prepass: the path from the copy hook at 20730 runs through both. -/
def cLook (n : Nat) : Option (BitVec 32) := match tailLook n with | some w => some w | none => h2Look n
theorem h2Look_ok {im : Image} (h : HooksAt im) : LookOK im h2Look := by
  intro n w hw
  obtain ⟨-, -, -, ⟨rest, hrest⟩⟩ := h
  unfold h2Look at hw
  split at hw
  · rename_i hle
    have hlen : n - 20813 < h2SignTail.length := (List.getElem?_eq_some_iff.mp hw).1
    have h2 : (im.code.drop 20813)[n - 20813]? = some w := by
      rw [← hrest, List.getElem?_append_left hlen]; exact hw
    rwa [List.getElem?_drop, Nat.add_sub_cancel' hle] at h2
  · cases hw
theorem cLook_ok {im : Image} (h1 : NewCodeAt im) (h2 : HooksAt im) : LookOK im cLook := by
  intro n w hw
  unfold cLook at hw
  split at hw
  · rename_i w' hw'
    cases hw
    exact tailLook_ok h1 n _ hw'
  · exact h2Look_ok h2 n w hw
theorem run_sound {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat}
    {n : Nat} {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState)
    (hpc : s.pc = pcOf n) (hobl : ∀ o ∈ r.st.obl, o.holds s) (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps im s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound (known := []) h hl s hpc (by intro p hp; cases hp) hobl hbr
theorem PRes.toState_getReg' (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem' (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc' (r : PRes) (s : MachineState) (h : r.spc = none) : (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
end ClaudeWCT.W9.Machine.Sign
end
section
namespace ClaudeWCT.W9.Machine.Sign
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateInput header pad64 Coordinate
  HashOutput Digest)
section tb
variable {α β : Type} {im : Image} {sk : BitVec 256}
theorem TBSim.pure_steps' {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps im s k c t) (hQ : Q a t) : TBSim im sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq' {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim im sk s W p Q) (he : p = q) (hW : W = W') : TBSim im sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.publicHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind' {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind' {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim im sk (writeHash s a) W (f a) Q) :
    TBSim im sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privatePair_bind' {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim im sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq' (TBSim.privateHash_bind' hf ht0 hv hq h) rfl (by rw [hb])
end tb
theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; intro he; exact h ((ofNat_inj hA hk).mp he)
    rw [if_neg hne, if_neg h]
@[simp] theorem E_eval_c' (s : MachineState) (v : Word) : (E.c v).eval s = v := rfl
@[simp] theorem E_eval_reg' (s : MachineState) (r : Reg) : (E.reg r).eval s = s.getReg r := rfl
end ClaudeWCT.W9.Machine.Sign
end
end
end
-- ==== merged from T3M_Keygen_PackedInput ====
section

namespace SigGolfCandidate.T3M.Keygen.Packed
open SigGolfCandidate.T3 (Layer Digest height chainHeader chainInput zero16 pad64)
open SphincsSecurity (bytesLE bytesLE_length)
theorem wordsOf_chainInput (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (chainInput lay tree leaf i step v) =
      [0, 0, (chainHeader lay tree leaf i step).extractLsb' 0 64,
        (chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  unfold chainInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [zero16]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl
theorem query_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  have hl : (chainInput lay tree leaf i step v).length = 64 := by
    simp [chainInput, bytesLE_length, zero16]
  rw [pad64_of_aligned _ (by rw [hl]), blocks_toQ ⟨by rw [hl]; omega, by rw [hl]⟩, hl]
end SigGolfCandidate.T3M.Keygen.Packed
end
-- ==== merged from T3M_Keygen_PackedFactories ====
section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def keygen_entry : List (BitVec 32) := [0x7340006f]
sym_block run_keygen_entry := symRun { noAlias := true } keygen_entry (pcOf 126) 100
def keygen_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_keygen_layer0 := symRun { noAlias := true } keygen_layer0 (pcOf 587) 100
def keygen_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_keygen_layer1 := symRun { noAlias := true } keygen_layer1 (pcOf 589) 100
def keygen_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_keygen_layer23 := symRun { noAlias := true } keygen_layer23 (pcOf 591) 100
def keygen_inc : List (BitVec 32) := [6521747]
sym_block run_keygen_inc := symRun { noAlias := true } keygen_inc (pcOf 592) 100
def keygen_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0x885ff06f]
sym_block run_keygen_body := symRun { noAlias := true } keygen_body (pcOf 593) 100
/-- Witness stack: the keygen header store ends at 134 (`lui t3; addi t3; sd t1,16(t3)`); 135 jumps to the G/F step
block at 689. -/
def keygen_store : List (BitVec 32) := [134711,437128723,7223331]
sym_block run_keygen_store := symRun { noAlias := true } keygen_store (pcOf 132) 100
def sign_entry : List (BitVec 32) := [0x7340006f]
sym_block run_sign_entry := symRun { noAlias := true } sign_entry (pcOf 1022) 100
def sign_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_sign_layer0 := symRun { noAlias := true } sign_layer0 (pcOf 1483) 100
def sign_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_sign_layer1 := symRun { noAlias := true } sign_layer1 (pcOf 1485) 100
def sign_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_sign_layer23 := symRun { noAlias := true } sign_layer23 (pcOf 1487) 100
def sign_inc : List (BitVec 32) := [6521747]
sym_block run_sign_inc := symRun { noAlias := true } sign_inc (pcOf 1488) 100
def sign_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0x885ff06f]
sym_block run_sign_body := symRun { noAlias := true } sign_body (pcOf 1489) 100
/-- Pairing stage 1: the sign header store ends at 1030 (`lui t3; addi t3; sd t1,16(t3)`); 1031 jumps to the G/F
step block at 1732. -/
def sign_store : List (BitVec 32) := [134711,437128723,7223331]
sym_block run_sign_store := symRun { noAlias := true } sign_store (pcOf 1028) 100
def expand_entry : List (BitVec 32) := [901775471]
sym_block run_expand_entry := symRun { noAlias := true } expand_entry (pcOf 1032) 100
def expand_layer0 : List (BitVec 32) := [0xc00393,264803]
sym_block run_expand_layer0 := symRun { noAlias := true } expand_layer0 (pcOf 1247) 100
def expand_layer1 : List (BitVec 32) := [1049491,7603299]
sym_block run_expand_layer1 := symRun { noAlias := true } expand_layer1 (pcOf 1249) 100
def expand_layer23 : List (BitVec 32) := [915,6521747]
sym_block run_expand_layer23 := symRun { noAlias := true } expand_layer23 (pcOf 1251) 100
def expand_inc : List (BitVec 32) := [6521747]
sym_block run_expand_inc := symRun { noAlias := true } expand_inc (pcOf 1252) 100
def expand_body : List (BitVec 32) := [7639859,19071795,134711,437128723,33772435,8272931,33755923,16995091,50598803,7562035,0xc100f13,59711251,31679283,0xffa7393,8622995,7562035,0x809e393,7562035,0xc5dff06f]
sym_block run_expand_body := symRun { noAlias := true } expand_body (pcOf 1253) 100
/-- Pairing stage 1 (expand side, edited by pair1-sign only so that this shared file builds): the store ends at 1040;
1041 jumps to the G/F step block at 43764. -/
def expand_store : List (BitVec 32) := [134711,437128723,7223331]
sym_block run_expand_store := symRun { noAlias := true } expand_store (pcOf 1038) 100
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
-- ==== merged from T3M_Keygen_PackedBlocks ====
section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance
theorem codeAt_keygen_entry : CodeAt Images.keygenImage (pcOf 126) keygen_entry := by decide +kernel
theorem steps_keygen_entry (s : MachineState) (hpc : s.pc = pcOf 126) :
    Steps Images.keygenImage s 1 1 (run_keygen_entry.res.toState s) := by
  exact symRun_sound run_keygen_entry codeAt_keygen_entry s hpc (by simp [run_keygen_entry.res, rv_simp])
theorem codeAt_keygen_layer0 : CodeAt Images.keygenImage (pcOf 587) keygen_layer0 := by decide +kernel
theorem steps_keygen_layer0 (s : MachineState) (hpc : s.pc = pcOf 587) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer0.res.toState s) := by
  exact symRun_sound run_keygen_layer0 codeAt_keygen_layer0 s hpc (by simp [run_keygen_layer0.res, rv_simp])
theorem codeAt_keygen_layer1 : CodeAt Images.keygenImage (pcOf 589) keygen_layer1 := by decide +kernel
theorem steps_keygen_layer1 (s : MachineState) (hpc : s.pc = pcOf 589) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer1.res.toState s) := by
  exact symRun_sound run_keygen_layer1 codeAt_keygen_layer1 s hpc (by simp [run_keygen_layer1.res, rv_simp])
theorem codeAt_keygen_layer23 : CodeAt Images.keygenImage (pcOf 591) keygen_layer23 := by decide +kernel
theorem steps_keygen_layer23 (s : MachineState) (hpc : s.pc = pcOf 591) :
    Steps Images.keygenImage s 2 2 (run_keygen_layer23.res.toState s) := by
  exact symRun_sound run_keygen_layer23 codeAt_keygen_layer23 s hpc (by simp [run_keygen_layer23.res, rv_simp])
theorem codeAt_keygen_inc : CodeAt Images.keygenImage (pcOf 592) keygen_inc := by decide +kernel
theorem steps_keygen_inc (s : MachineState) (hpc : s.pc = pcOf 592) :
    Steps Images.keygenImage s 1 1 (run_keygen_inc.res.toState s) := by
  exact symRun_sound run_keygen_inc codeAt_keygen_inc s hpc (by simp [run_keygen_inc.res, rv_simp])
theorem codeAt_keygen_body : CodeAt Images.keygenImage (pcOf 593) keygen_body := by decide +kernel
theorem steps_keygen_body (s : MachineState) (hpc : s.pc = pcOf 593) :
    Steps Images.keygenImage s 19 19 (run_keygen_body.res.toState s) := by
  exact symRun_sound run_keygen_body codeAt_keygen_body s hpc (by simp [run_keygen_body.res, rv_simp])
theorem codeAt_keygen_store : CodeAt Images.keygenImage (pcOf 132) keygen_store := by decide +kernel
theorem steps_keygen_store (s : MachineState) (hpc : s.pc = pcOf 132) :
    Steps Images.keygenImage s 3 3 (run_keygen_store.res.toState s) := by
  exact symRun_sound run_keygen_store codeAt_keygen_store s hpc (by simp [run_keygen_store.res, rv_simp])
theorem codeAt_sign_entry : CodeAt Images.signReferenceImage (pcOf 1022) sign_entry := by decide +kernel
theorem steps_sign_entry (s : MachineState) (hpc : s.pc = pcOf 1022) :
    Steps Images.signReferenceImage s 1 1 (run_sign_entry.res.toState s) := by
  exact symRun_sound run_sign_entry codeAt_sign_entry s hpc (by simp [run_sign_entry.res, rv_simp])
theorem codeAt_sign_layer0 : CodeAt Images.signReferenceImage (pcOf 1483) sign_layer0 := by decide +kernel
theorem steps_sign_layer0 (s : MachineState) (hpc : s.pc = pcOf 1483) :
    Steps Images.signReferenceImage s 2 2 (run_sign_layer0.res.toState s) := by
  exact symRun_sound run_sign_layer0 codeAt_sign_layer0 s hpc (by simp [run_sign_layer0.res, rv_simp])
theorem codeAt_sign_layer1 : CodeAt Images.signReferenceImage (pcOf 1485) sign_layer1 := by decide +kernel
theorem steps_sign_layer1 (s : MachineState) (hpc : s.pc = pcOf 1485) :
    Steps Images.signReferenceImage s 2 2 (run_sign_layer1.res.toState s) := by
  exact symRun_sound run_sign_layer1 codeAt_sign_layer1 s hpc (by simp [run_sign_layer1.res, rv_simp])
theorem codeAt_sign_layer23 : CodeAt Images.signReferenceImage (pcOf 1487) sign_layer23 := by decide +kernel
theorem steps_sign_layer23 (s : MachineState) (hpc : s.pc = pcOf 1487) :
    Steps Images.signReferenceImage s 2 2 (run_sign_layer23.res.toState s) := by
  exact symRun_sound run_sign_layer23 codeAt_sign_layer23 s hpc (by simp [run_sign_layer23.res, rv_simp])
theorem codeAt_sign_inc : CodeAt Images.signReferenceImage (pcOf 1488) sign_inc := by decide +kernel
theorem steps_sign_inc (s : MachineState) (hpc : s.pc = pcOf 1488) :
    Steps Images.signReferenceImage s 1 1 (run_sign_inc.res.toState s) := by
  exact symRun_sound run_sign_inc codeAt_sign_inc s hpc (by simp [run_sign_inc.res, rv_simp])
theorem codeAt_sign_body : CodeAt Images.signReferenceImage (pcOf 1489) sign_body := by decide +kernel
theorem steps_sign_body (s : MachineState) (hpc : s.pc = pcOf 1489) :
    Steps Images.signReferenceImage s 19 19 (run_sign_body.res.toState s) := by
  exact symRun_sound run_sign_body codeAt_sign_body s hpc (by simp [run_sign_body.res, rv_simp])
theorem codeAt_sign_store : CodeAt Images.signReferenceImage (pcOf 1028) sign_store := by decide +kernel
theorem steps_sign_store (s : MachineState) (hpc : s.pc = pcOf 1028) :
    Steps Images.signReferenceImage s 3 3 (run_sign_store.res.toState s) := by
  exact symRun_sound run_sign_store codeAt_sign_store s hpc (by simp [run_sign_store.res, rv_simp])
theorem codeAt_expand_entry : CodeAt Images.expandReferenceImage (pcOf 1032) expand_entry := by decide +kernel
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps Images.expandReferenceImage s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry codeAt_expand_entry s hpc (by simp [run_expand_entry.res, rv_simp])
theorem codeAt_expand_layer0 : CodeAt Images.expandReferenceImage (pcOf 1247) expand_layer0 := by decide +kernel
theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 1247) :
    Steps Images.expandReferenceImage s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 codeAt_expand_layer0 s hpc (by simp [run_expand_layer0.res, rv_simp])
theorem codeAt_expand_layer1 : CodeAt Images.expandReferenceImage (pcOf 1249) expand_layer1 := by decide +kernel
theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 1249) :
    Steps Images.expandReferenceImage s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 codeAt_expand_layer1 s hpc (by simp [run_expand_layer1.res, rv_simp])
theorem codeAt_expand_layer23 : CodeAt Images.expandReferenceImage (pcOf 1251) expand_layer23 := by decide +kernel
theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 1251) :
    Steps Images.expandReferenceImage s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 codeAt_expand_layer23 s hpc (by simp [run_expand_layer23.res, rv_simp])
theorem codeAt_expand_inc : CodeAt Images.expandReferenceImage (pcOf 1252) expand_inc := by decide +kernel
theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 1252) :
    Steps Images.expandReferenceImage s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc codeAt_expand_inc s hpc (by simp [run_expand_inc.res, rv_simp])
theorem codeAt_expand_body : CodeAt Images.expandReferenceImage (pcOf 1253) expand_body := by decide +kernel
theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 1253) :
    Steps Images.expandReferenceImage s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body codeAt_expand_body s hpc (by simp [run_expand_body.res, rv_simp])
theorem codeAt_expand_store : CodeAt Images.expandReferenceImage (pcOf 1038) expand_store := by decide +kernel
theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps Images.expandReferenceImage s 3 3 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store codeAt_expand_store s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
-- ==== merged from T3M_Keygen_PackedRun ====
section

section
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def routed (s : MachineState) : Word :=
  (s.getReg .x9 <<< ((s.getReg .x7).toNat % 64)) + s.getReg .x18
def packedWord (s : MachineState) : Word :=
  ((routed s <<< 32) >>> 16) ||| (s.getReg .x8 <<< 48) ||| (193#64 <<< 56) |||
    ((s.getReg .x20 &&& 255#64) <<< 8) ||| (s.getReg .x19 ||| 128#64)
structure BodyPost (s t : MachineState) : Prop where
  low : t.getReg .x6 = packedWord s
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routed s >>> 32
  regs : RegsExcept s t [.x6, .x7, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 24)
theorem keygen_body_post (s : MachineState) : BodyPost s (run_keygen_body.res.toState s) := by
  constructor
  · simp [run_keygen_body.res, rv_simp, packedWord, routed]
  · simp [run_keygen_body.res, rv_simp, routed]
  · intro r hr
    cases r <;> simp_all [run_keygen_body.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, run_keygen_body.res]
    t3n []
    rw [if_neg (by omega)]
theorem keygen_body_spec (s : MachineState) (hpc : s.pc = pcOf 593) :
    ∃ t, Steps Images.keygenImage s 19 19 t ∧ t.pc = pcOf 132 ∧ BodyPost s t := by
  exact ⟨_, steps_keygen_body s hpc, by simp [run_keygen_body.res, rv_simp], keygen_body_post s⟩
theorem sign_body_post (s : MachineState) : BodyPost s (run_sign_body.res.toState s) := by
  have h := keygen_body_post s
  exact ⟨h.low, h.high, h.regs, h.frame⟩
theorem sign_body_spec (s : MachineState) (hpc : s.pc = pcOf 1489) :
    ∃ t, Steps Images.signReferenceImage s 19 19 t ∧ t.pc = pcOf 1028 ∧ BodyPost s t := by
  exact ⟨_, steps_sign_body s hpc, by simp [run_sign_body.res, rv_simp], sign_body_post s⟩
theorem expand_body_post (s : MachineState) : BodyPost s (run_expand_body.res.toState s) := by
  have h := keygen_body_post s
  exact ⟨h.low, h.high, h.regs, h.frame⟩
theorem expand_body_spec (s : MachineState) (hpc : s.pc = pcOf 1253) :
    ∃ t, Steps Images.expandReferenceImage s 19 19 t ∧ t.pc = pcOf 1038 ∧ BodyPost s t := by
  exact ⟨_, steps_expand_body s hpc, by simp [run_expand_body.res, rv_simp], expand_body_post s⟩
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
section
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def routedAt (s : MachineState) (height : Nat) : Word :=
  (s.getReg .x9 <<< height) + s.getReg .x18
def packedAt (s : MachineState) (height : Nat) : Word :=
  ((routedAt s height <<< 32) >>> 16) ||| (s.getReg .x8 <<< 48) ||| (193#64 <<< 56) |||
    ((s.getReg .x20 &&& 255#64) <<< 8) ||| (s.getReg .x19 ||| 128#64)
/-- Witness stack: the keygen header ends at 135 (`jal 689`, the G/F step block) with `t3 = CHAIN` and no HASH
arguments set. -/
structure HeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  x28 : t.getReg .x28 = BitVec.ofNat 64 0x201A0
  regs : RegsExcept s t [.x6, .x7, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)
theorem keygen_header_0 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps Images.keygenImage s 25 25 t ∧ t.pc = pcOf 135 ∧ HeaderPost s t 12 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_body.res.toState s1
  have h2 := steps_keygen_body s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_store.res.toState s2
  have h3 := steps_keygen_store s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s3, ((h0.trans h1).trans h2).trans h3, ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [s3, s2, s1, s0, Result.toState_getMem, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
end
-- ==== merged from T3M_Keygen_Blocks ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seg_0 : List (BitVec 32) := [659,0x8000e93,134967,963331,9352067,7286819,8336419,0x9000e93,134967,34541331,963331,9352067,7286819,8336419,134967,34551843,34552867,1043,1171,0x3300d13,53480851,3987,133943,0x460b0b13,327991,2323]
def seg_26 : List (BitVec 32) := [4919,40456803]
def seg_28 : List (BitVec 32) := [138167,0xa00b8b93,6882227,4428691,2329779,465567983]
def seg_34 : List (BitVec 32) := [1640723,0xfddff06f]
/-- C4: word 37 is `addi s5,zero,0` (the top label's base word is 0; it was 64). -/
def seg_36 : List (BitVec 32) := [12584851,2707,805306607]
def seg_39 : List (BitVec 32) := [998244463,16855811,25244547,7286819,8336419,39991,34343955,0x40000a13,2098835]
def seg_48 : List (BitVec 32) := [1049363,0x86a0663]
def seg_50 : List (BitVec 32) := [2451]
def seg_51 : List (BitVec 32) := [0x749dc63]
def seg_52 : List (BitVec 32) := [4919,0xd0130313,33988371,31679283,34182035,134711,7223331,8272931,132407,67110291,132663,0x6060613]
def seg_64 : List (BitVec 32) := [115]
def seg_65 : List (BitVec 32) := [20581939,5119507,3018291,930563,9319299,134839,0x60e8e93,966147,9354883,29573939,30655411,7090211,8139811,17566739,1673619,0xf8dff06f]
def seg_81 : List (BitVec 32) := [1726995,1476243,0xf75ff06f]
def seg_84 : List (BitVec 32) := [0x8000e93,40759,0xfe0f0f13,963331,9352067,7286819,8336419,0x9000e93,40759,963331,9352067,7286819,8336419,40759,0xfe0f0f13,34551843,34552867,4919,0xe0130313,915,40503,0xfe0e0e13,7223331,8272931,38199,0xfe050513,34231,67470739,38455]
def seg_113 : List (BitVec 32) := [115]
def seg_114 : List (BitVec 32) := [1049235,1299]
def seg_116 : List (BitVec 32) := [115]
def seg_277 : List (BitVec 32) := [327991,65811,0xa000f13,16855811,25244547,7286819,8336419,527415,34343955,6711,657939,2835]
def seg_289 : List (BitVec 32) := [2963,1727763,4856467,327991,65811,2788019]
def seg_295 : List (BitVec 32) := [4919,0xd0130313,34280339,7562035,34313107,134711,921107,7223331,8272931,132407,328979,67110291,132663,0x6060613]
def seg_309 : List (BitVec 32) := [115]
def seg_310 : List (BitVec 32) := [701187,406403,7553843,7090211,9089795,8795011,7553843,7091235,17478403,17183619,7553843,7092259,25867011,25572227,7553843,7093283,34245267,34343955,1805203,0xf7abece3]
def seg_330 : List (BitVec 32) := [1726995,1772307,0xc00313,0xf46b68e3]
def seg_334 : List (BitVec 32) := [134711,921107,3767,0x80e8e93,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,0xe0130313,7223331,932899,132407,328979,67110291,460343,394771,115,1049363,33755923,7224355,460343,33949203,115,0xfff00913,3758355,657847,625043,461623,723731,527543,822419,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb023,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb423,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecb823,17500947,736131,19659699,9124867,526007,33982099,1811,452483,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,4646787,0xe787b3,58177587,58165171,3676179,64477331,18352179,19396531,0xf80833,64509715,19429427,17237811,8816275,0xf9369ee3,64444307,19363635,0xf70733,19351475,1554323,0xfff78793,0xf77733,25626419,0xecbc23,1049235,1299,115]
def sub_0 : List (BitVec 32) := [2579]
def sub_1 : List (BitVec 32) := [18488931]
def sub_2 : List (BitVec 32) := [134839,487493267,963331,9352067,7057443,8107043]
def sub_8 : List (BitVec 32) := [89785443]
def sub_9 : List (BitVec 32) := [0x7340006f,21201843,33788691,17047315,31679283,269706003,134711,437128723,7223331,132407,436536595,67110291,132663,486934035]
def sub_23 : List (BitVec 32) := [115]
def sub_24 : List (BitVec 32) := [1706515,0xfa1ff06f]
def sub_26 : List (BitVec 32) := [32871]
def sub_27 : List (BitVec 32) := [33171,17371923,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,19,2451]
def sub_41 : List (BitVec 32) := [0xda9dc63]
def sub_42 : List (BitVec 32) := [1700627,67310179]
def sub_44 : List (BitVec 32) := [1695251,17044243,34479891,31679283,1270547,295827,34152211,31712179,134711,7223331,8272931,132407,67110291,132663,67503635]
def sub_59 : List (BitVec 32) := [115]
def sub_60 : List (BitVec 32) := [1703443,5119507,134839,68062867,31329843,134967,487526163,930563,9319299,7286819,8336419,20647475]
def sub_72 : List (BitVec 32) := [936067]
def sub_73 : List (BitVec 32) := [7342739,267363]
def sub_75 : List (BitVec 32) := [0x6750006f]
def sub_76 : List (BitVec 32) := [0xf8463]
def sub_77 : List (BitVec 32) := [559763]
def sub_78 : List (BitVec 32) := [0xec9ff0ef]
def sub_79 : List (BitVec 32) := [34576995]
def sub_80 : List (BitVec 32) := [4824595,17698323]
def sub_82 : List (BitVec 32) := [17698323]
def sub_83 : List (BitVec 32) := [134839,0x600e8e93,31329843,134839,487493267,963331,9352067,7221283,8270883]
def sub_92 : List (BitVec 32) := [17533843,1673619,0xf2dff06f]
def sub_95 : List (BitVec 32) := [68129379]
def sub_96 : List (BitVec 32) := [1901331,4395795,66257683,0xfc037313,132407,0x60050513,198035,132663,0x3c060613]
def sub_105 : List (BitVec 32) := [115]
def sub_106 : List (BitVec 32) := [134839,0x3c0e8e93,963331,9352067,7122979,8172579]
def sub_112 : List (BitVec 32) := [98407]
def sub_113 : List (BitVec 32) := [1051155,0xfff78313,6953523]
def sub_116 : List (BitVec 32) := [0xa0a0663]
def sub_117 : List (BitVec 32) := [658451]
def sub_118 : List (BitVec 32) := [1708819,0x86c5c63]
def sub_120 : List (BitVec 32) := [6037011,3018291,134967,537857811,930563,9319299,7286819,8336419,134967,588189459,17707779,26096515,7286819,8336419,33857043,30073651,0xfe6f3023,55221779,787347,0x580e42e3]
def sub_140 : List (BitVec 32) := [0xfe7f3423,132407,537199891,67110291,132663,604374547]
def sub_146 : List (BitVec 32) := [115]
def sub_147 : List (BitVec 32) := [4988435,3018291,134839,604933779,963331,9352067,7221283,8270883,1838099,0xf69ff06f]
def sub_157 : List (BitVec 32) := [1726995,0xf59ff06f]
def sub_159 : List (BitVec 32) := [32871]
def revCode : List (BitVec 32) := [787347,0xff3f313,8590099,8639379,6546355,7735,0xf0fe0e13,29618995,4395795,4445075,29619123,6546355,15927,859704851,29618995,2298643,2347923,29619123,6546355,24119,0x555e0e13,29618995,1250067,1299347,29619123,6546355,50566035,0xa14ff06f]
def subL : Rv.Layout := [(0, sub_0), (1, sub_1), (2, sub_2), (8, sub_8), (9, sub_9), (23, sub_23), (24, sub_24), (26, sub_26), (27, sub_27), (41, sub_41), (42, sub_42), (44, sub_44), (59, sub_59), (60, sub_60), (72, sub_72), (73, sub_73), (75, sub_75), (76, sub_76), (77, sub_77), (78, sub_78), (79, sub_79), (80, sub_80), (82, sub_82), (83, sub_83), (92, sub_92), (95, sub_95), (96, sub_96), (105, sub_105), (106, sub_106), (112, sub_112), (113, sub_113), (116, sub_116), (117, sub_117), (118, sub_118), (120, sub_120), (140, sub_140), (146, sub_146), (147, sub_147), (157, sub_157), (159, sub_159)]
def subCode : List (BitVec 32) := layoutCode subL
theorem subL_ok : layoutOk 0 subL = true := by decide +kernel
def maxLow : List (BitVec 32) := [3148435,0x99b9d663]
def maxHigh : List (BitVec 32) := [4197011,0x984ff06f]
def maxLayout : Rv.Layout := [(0, maxLow), (2, maxHigh)]
def maxDigitCode : List (BitVec 32) := layoutCode maxLayout
theorem maxLayout_ok : layoutOk 0 maxLayout = true := by decide +kernel
def packedHelper : List (BitVec 32) :=
  PackedBlocks.keygen_layer0 ++ PackedBlocks.keygen_layer1 ++
    PackedBlocks.keygen_layer23 ++ PackedBlocks.keygen_body
/-! Campaign T8D (TOP2 NF17): the keygen image's leaf subroutine differs from `subL` (which stays the sign image's
leaf code, used by the sign proofs) at offsets 27 (leaf entry, now ending in `jal ra, COEFGEN`), 42 (`addi a3,s3,1;
jal ra, HORN`), 44 (`j 188`, the rest of the old seed-pair block is dead) and 75 (`j CAP`). The new routines COEFGEN
(612..640), HORN (642..682) and the per-chain cap table CAP (684..688) sit in the NOP run after the packed helper. -/
def sub27K : List (BitVec 32) := [33171,17371923,538141459,50601747,31679283,202379027,59711251,31679283,134711,1611533843,7223331,932899,19,1908408559]
def sub42K : List (BitVec 32) := [1672851,2021654767]
def sub44K : List (BitVec 32) := [113246319,17044243,34479891,31679283,1270547,295827,34152211,31712179,134711,7223331,8272931,132407,67110291,132663,67503635]
def sub75K : List (BitVec 32) := [2063597679]
/-- Campaign T51 (endpad top leaf): offsets 80..82 (words 197..199) compute the leaf slot `16 (i + [i ≠ 0])`:
`sltu t5, zero, s3; add t3, s3, t5; slli t3, t3, 4` (the sign keeps `sub_80`, `sub_82`). -/
def sub80K : List (BitVec 32) := [0x1303f33,0x1e98e33]
def sub82K : List (BitVec 32) := [0x4e1e13]
/-- Witness stack: offset 9 (the header block) ends its 10th word in `jal 689` (the G/F step block). -/
def sub9K : List (BitVec 32) := [0x7340006f,21201843,33788691,17047315,31679283,269706003,134711,437128723,7223331,
  0x0a90006f,436536595,67110291,132663,486934035]
/-! C4 (top-tree spill-down; the keygen words are b3cc11b's, byte-identical): the keygen's top leaf exit (offsets 96, 106)
and tree node (120, 140, 147) select the answer half by parity (`ld 16(t4)` for an even index) and write the one-word
label `(s5 | tree << 32) + heap` with a zero high word. The sign keeps `sub_96`, `sub_106`, `sub_120`, `sub_140`,
`sub_147` (its own copies at 1013). -/
def sub96K : List (BitVec 32) := [1901971,4560275,66422163,0xfc05f593,132407,0x60050513,132663,1007027731,1670803]
def sub106K : List (BitVec 32) := [5152403,0x41d60eb3,17740547,26129283,7122979,8172579]
def sub120K : List (BitVec 32) := [6037011,3018291,134967,537857811,930563,9319299,7286819,8336419,134967,588189459,17707779,26096515,7286819,8336419,33857043,30073651,25363251,0xfe6f3023,0xfe0f3423,1867411]
def sub140K : List (BitVec 32) := [5152403,132407,537199891,67110291,132663,604374547]
/-- Top-bytes layer: keygen hooks `230 -> jal 721` (KINIT) and `274 -> jal 724` (KNEXT); offsets 113 and 157 of
the keygen subroutine (the sign keeps `sub_113`, `sub_157`). -/
def sub113K : List (BitVec 32) := [0x7ac0006f,0xfff78313,6953523]
def sub157K : List (BitVec 32) := [0x7080006f,0xf59ff06f]
def sub147K : List (BitVec 32) := [0x73c0006f,3018291,0x41d60eb3,17740547,26129283,7221283,8270883,19,1838099,0xf69ff06f]
/-- Offsets where the keygen's leaf subroutine differs from `subL` (T8D: 27, 42, 44, 75; C4: 96, 106, 120, 140, 147). -/
def kOwn (off : Nat) : Bool := off = 27 || off = 42 || off = 44 || off = 75 || off = 96 || off = 106 || off = 120 ||
  off = 140 || off = 147 || off = 113 || off = 157 || off = 9 || off = 80 || off = 82
/-- The keygen copy of the leaf subroutine (offsets relative to 117). -/
def kSubL : Rv.Layout := subL.map fun p =>
  if p.1 = 27 then (27, sub27K) else if p.1 = 42 then (42, sub42K) else if p.1 = 44 then (44, sub44K)
  else if p.1 = 75 then (75, sub75K) else if p.1 = 96 then (96, sub96K) else if p.1 = 106 then (106, sub106K)
  else if p.1 = 120 then (120, sub120K) else if p.1 = 140 then (140, sub140K) else if p.1 = 147 then (147, sub147K)
  else if p.1 = 113 then (113, sub113K) else if p.1 = 157 then (157, sub157K)
  else if p.1 = 9 then (9, sub9K) else if p.1 = 80 then (80, sub80K) else if p.1 = 82 then (82, sub82K) else p
theorem kSubL_ok : layoutOk 0 kSubL = true := by decide +kernel
/-- COEFGEN (612..640): the 12 private pairs `privatePair 0 0 0 (12 leaf + j) 0` into the 24 coefficients at COEF. -/
def coefgenCode : List (BitVec 32) := [0x650006f,0x600f13,65603379,34019091,1533715,3731,132407,15022115,343075,67110291,67438099,115,67449347,4993059,75837955,4994083,84226563,4995107,92615171,4996131,34343955,1052435,34545427,31917875,2002579,0x1000f13,4226717923,2451,32871]
/-- HORN (642..682): `familyEval coefs a3` into CHAIN + 48. -/
def hornCode : List (BitVec 32) := [0x3d0006f,1939,136503,0xc050513,136631,4278519059,2067,3091,531,1555,429715,2031379,985187,15222835,16534579,12730931,66576147,1447443,31876659,66543379,1546131,31975347,1513235,2023059,4228814563,1187603,32000051,2236179,32000051,7479059,32000051,4737075,343811,31999795,8732419,32262067,4172616419,134967,485439523,486489123,32871]
/-- CAP (684..688): `s5 = maxDigit 0 s3` (4 below chain 51, else 7). -/
def capCode : List (BitVec 32) := [0x500a93,0x1b00f13,2246690531,0x400a93,0x1480006f]
/-- Top-bytes layer (opus-topbytes A): KINIT 721..723, KNEXT 724..726, KCHK 727..759 (node nonce loop), KOK
760..769 (pad reset + the original node store, then `jal 272`). Words 689..720 are the opus-wstack G/F step block (`kgStepCode`). -/
def kchkCode : List (BitVec 32) := [0x100a13,0x100693,0x851ff06f,0x1a5a13,0x168693,0x84dff06f,0xc00e13,0x9c68063,0xffd68713,0x300e13,0x7c6ca63,0x71863,0x100713,0x80006f,0x800713,0x4000e13,0x40ee0e33,0xfff00813,0x1c81833,0xb00e13,0x1c69663,0xff00813,0x2881813,0x6800893,0xe898b3,0x41d60f33,0x18f3f03,0x10f7f33,0x20f0663,0x20e37,0x220e3f03,0x1f0f13,0x11f7e63,0x23ee3023,0x20537,0x20050513,0x4000593,0x73,0xfcdff06f,0x20e37,0x220e3023,0x4c1e13,0x2e0e33,0x41d60eb3,0x10eb303,0x18eb383,0x6e3023,0x7e3423,0x83dff06f]
/-- img-v6: KTOP (1149..1168, top family coefficients: `s2 & 3 ≠ 0` returns; else first pair `(39 f + (f & 1)) / 2`,
odd `f` copies the carry slot 39 to slot 0; `jal 618`) and KHORN (1169..1176: point `a3 += (s2 & 3) << 6`, 39
coefficients, `jal 647`). -/
def ktopCode : List (BitVec 32) := [0x397f13,0x40f1263,0x21c37,0x295f13,0x1f7e93,0x1f00713,0x2ef0733,0x1d70733,0x175713,0x2071713,0x176713,0xe8c63,0x1f0c3203,0x4c3023,0x1f8c3203,0x4c3423,0x10c0c13,0xf70ff06f,0x993,0x8067,0x397f13,0x6f1f13,0x1e686b3,0x713,0x793,0x215b7,0x1f058513,0xfbcff06f]
/-- Witness stack (charge 86): the top G/F chain step block (689..720, entered by `jal 689` at 135). -/
def kgStepCode : List (BitVec 32) := [0x6041263,0x19f313,0x393,0x4731c63,0x3400393,0x533c863,0x10e3303,0x46e3023,0x18e3303,0x46e3423,0x40e3823,0x40e3c23,0x60e3023,0x60e3423,0x30e0513,0x4000593,0x20e0613,0xfffa8313,0x3300393,0x99463,0xa8313,0x6a1463,0x30e0613,0x73,0xf10ff06f,0x20e3023,0x20e3423,0xe0513,0x4000593,0x30e0613,0x73,0xef4ff06f]
/-- Campaign T51: CAP continuation (770..776, former NOPs): `i < 48 → 4`, `i < 50 → 6`, else `5`, then `j 193`. -/
def capCont : List (BitVec 32) := [0x3000f13,0xefe9cc63,0x600a93,0x3200f13,0xefe9c663,0x500a93,0xee4ff06f]
def seg_542 : List (BitVec 32) :=
  List.replicate 45 0x00000013 ++ packedHelper ++ coefgenCode ++ [0x00000013] ++ hornCode ++ [0x00000013] ++
    capCode ++ kgStepCode ++ kchkCode ++ capCont ++ List.replicate 340 0x00000013
def mainL : Rv.Layout := [(0, seg_0), (26, seg_26), (28, seg_28), (34, seg_34), (36, seg_36), (39, seg_39), (48, seg_48), (50, seg_50), (51, seg_51), (52, seg_52), (64, seg_64), (65, seg_65), (81, seg_81), (84, seg_84), (113, seg_113), (114, seg_114), (116, seg_116), (117, layoutCode kSubL), (277, seg_277), (289, seg_289), (295, seg_295), (309, seg_309), (310, seg_310), (330, seg_330), (334, seg_334), (542, seg_542), (1117, maxDigitCode), (1121, revCode), (1149, ktopCode)]
theorem mainL_ok : layoutOk 0 mainL = true := by decide +kernel
abbrev image : Image := Images.keygenImage
theorem code_eq : image.code = layoutCode mainL := by decide +kernel
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_layout code_eq mainL_ok (i := 0) (by kernel_rfl) (by decide)
theorem codeAt_26 : CodeAt image (pcOf 26) seg_26 :=
  codeAt_layout code_eq mainL_ok (i := 1) (by kernel_rfl) (by decide)
theorem codeAt_28 : CodeAt image (pcOf 28) seg_28 :=
  codeAt_layout code_eq mainL_ok (i := 2) (by kernel_rfl) (by decide)
theorem codeAt_34 : CodeAt image (pcOf 34) seg_34 :=
  codeAt_layout code_eq mainL_ok (i := 3) (by kernel_rfl) (by decide)
theorem codeAt_36 : CodeAt image (pcOf 36) seg_36 :=
  codeAt_layout code_eq mainL_ok (i := 4) (by kernel_rfl) (by decide)
theorem codeAt_39 : CodeAt image (pcOf 39) seg_39 :=
  codeAt_layout code_eq mainL_ok (i := 5) (by kernel_rfl) (by decide)
theorem codeAt_48 : CodeAt image (pcOf 48) seg_48 :=
  codeAt_layout code_eq mainL_ok (i := 6) (by kernel_rfl) (by decide)
theorem codeAt_50 : CodeAt image (pcOf 50) seg_50 :=
  codeAt_layout code_eq mainL_ok (i := 7) (by kernel_rfl) (by decide)
theorem codeAt_51 : CodeAt image (pcOf 51) seg_51 :=
  codeAt_layout code_eq mainL_ok (i := 8) (by kernel_rfl) (by decide)
theorem codeAt_52 : CodeAt image (pcOf 52) seg_52 :=
  codeAt_layout code_eq mainL_ok (i := 9) (by kernel_rfl) (by decide)
theorem codeAt_64 : CodeAt image (pcOf 64) seg_64 :=
  codeAt_layout code_eq mainL_ok (i := 10) (by kernel_rfl) (by decide)
theorem codeAt_65 : CodeAt image (pcOf 65) seg_65 :=
  codeAt_layout code_eq mainL_ok (i := 11) (by kernel_rfl) (by decide)
theorem codeAt_81 : CodeAt image (pcOf 81) seg_81 :=
  codeAt_layout code_eq mainL_ok (i := 12) (by kernel_rfl) (by decide)
theorem codeAt_84 : CodeAt image (pcOf 84) seg_84 :=
  codeAt_layout code_eq mainL_ok (i := 13) (by kernel_rfl) (by decide)
theorem codeAt_113 : CodeAt image (pcOf 113) seg_113 :=
  codeAt_layout code_eq mainL_ok (i := 14) (by kernel_rfl) (by decide)
theorem codeAt_114 : CodeAt image (pcOf 114) seg_114 :=
  codeAt_layout code_eq mainL_ok (i := 15) (by kernel_rfl) (by decide)
theorem codeAt_116 : CodeAt image (pcOf 116) seg_116 :=
  codeAt_layout code_eq mainL_ok (i := 16) (by kernel_rfl) (by decide)
theorem codeAt_kSubCode : CodeAt image (pcOf 117) (layoutCode kSubL) :=
  codeAt_layout code_eq mainL_ok (i := 17) (by kernel_rfl) (by apply of_decide_eq_true; kernel_rfl)
theorem codeAt_277 : CodeAt image (pcOf 277) seg_277 :=
  codeAt_layout code_eq mainL_ok (i := 18) (by kernel_rfl) (by decide)
theorem codeAt_289 : CodeAt image (pcOf 289) seg_289 :=
  codeAt_layout code_eq mainL_ok (i := 19) (by kernel_rfl) (by decide)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_layout code_eq mainL_ok (i := 20) (by kernel_rfl) (by decide)
theorem codeAt_309 : CodeAt image (pcOf 309) seg_309 :=
  codeAt_layout code_eq mainL_ok (i := 21) (by kernel_rfl) (by decide)
theorem codeAt_310 : CodeAt image (pcOf 310) seg_310 :=
  codeAt_layout code_eq mainL_ok (i := 22) (by kernel_rfl) (by decide)
theorem codeAt_330 : CodeAt image (pcOf 330) seg_330 :=
  codeAt_layout code_eq mainL_ok (i := 23) (by kernel_rfl) (by decide)
theorem codeAt_334 : CodeAt image (pcOf 334) seg_334 :=
  codeAt_layout code_eq mainL_ok (i := 24) (by kernel_rfl) (by apply of_decide_eq_true; kernel_rfl)
/-- The leaf subroutine at `b`, except the segments at the `kOwn` offsets (which differ between the keygen image and
`subL`, campaign T8D and C4). C4: only the keygen image (the sign uses `SeedIndependentAt`). -/
def SubAt (image : Image) (b : Nat) : Prop :=
  (∀ off code, (off, code) ∈ subL → kOwn off = false →
    CodeAt image (pcOf (b + off)) code) ∧ (b = 117 ∨ b = 1013) ∧
  (CodeAt image (pcOf (b + 1000)) maxDigitCode ∧ CodeAt image (pcOf (b + 1004)) revCode ∧
    (image = Images.keygenImage ∧ b = 117))
theorem codeAt_max : CodeAt image (pcOf 1117) maxDigitCode :=
  codeAt_layout code_eq mainL_ok (i := 26) (by kernel_rfl) (by decide)
theorem codeAt_1121 : CodeAt image (pcOf 1121) revCode :=
  codeAt_layout code_eq mainL_ok (i := 27) (by kernel_rfl) (by decide)
theorem codeAt_1149 : CodeAt image (pcOf 1149) ktopCode :=
  codeAt_layout code_eq mainL_ok (i := 28) (by kernel_rfl) (by decide)
theorem subAt_keygen : SubAt image 117 := by
  refine ⟨?_, Or.inl rfl, codeAt_max, codeAt_1121, rfl, rfl⟩
  intro off code hm hk
  simp only [kOwn, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h27, h42⟩, h44⟩, h75⟩, h96⟩, h106⟩, h120⟩, h140⟩, h147⟩, h113⟩, h157⟩, h9⟩, h80⟩, h82⟩ := hk
  have hp : (off, code) ∈ kSubL := List.mem_map.mpr ⟨(off, code), hm, by
    simp [h27, h42, h44, h75, h96, h106, h120, h140, h147, h113, h157, h9, h80, h82]⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  exact codeAt_sublayout codeAt_kSubCode kSubL_ok hi
/-- C4: a keygen-only segment of `kSubL` at `117 + off`. -/
theorem codeAt_kSub {image : Image} {b : Nat} (h : SubAt image b) {off : Nat} {code : List (BitVec 32)}
    (hm : (off, code) ∈ kSubL) : CodeAt image (pcOf (b + off)) code := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
  exact codeAt_sublayout codeAt_kSubCode kSubL_ok hi
theorem codeAt_rev {image : Image} {b : Nat} (h : SubAt image b) : CodeAt image (pcOf (b + 1004)) revCode :=
  h.2.2.2.1
theorem codeAt_maxLow {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1000)) maxLow := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 0) (o := 0) (seg := maxLow) (by kernel_rfl)
  simpa only [Nat.add_zero] using q
theorem codeAt_maxHigh {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1002)) maxHigh := by
  have q := codeAt_sublayout (L := maxLayout) (b := b + 1000) h.2.2.1 maxLayout_ok
    (i := 1) (o := 2) (seg := maxHigh) (by kernel_rfl)
  simpa [Nat.add_assoc] using q
theorem codeAt_sub_0 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 0)) sub_0 :=
  h.1 0 sub_0 (by decide +kernel) (by decide)
theorem codeAt_sub_1 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 1)) sub_1 :=
  h.1 1 sub_1 (by decide +kernel) (by decide)
theorem codeAt_sub_2 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 2)) sub_2 :=
  h.1 2 sub_2 (by decide +kernel) (by decide)
theorem codeAt_sub_8 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 8)) sub_8 :=
  h.1 8 sub_8 (by decide +kernel) (by decide)
theorem codeAt_sub9K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 9)) sub9K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_23 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 23)) sub_23 :=
  h.1 23 sub_23 (by decide +kernel) (by decide)
theorem codeAt_sub_24 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 24)) sub_24 :=
  h.1 24 sub_24 (by decide +kernel) (by decide)
theorem codeAt_sub_26 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 26)) sub_26 :=
  h.1 26 sub_26 (by decide +kernel) (by decide)
theorem codeAt_sub_41 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 41)) sub_41 :=
  h.1 41 sub_41 (by decide +kernel) (by decide)
theorem codeAt_sub_59 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 59)) sub_59 :=
  h.1 59 sub_59 (by decide +kernel) (by decide)
theorem codeAt_sub_60 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 60)) sub_60 :=
  h.1 60 sub_60 (by decide +kernel) (by decide)
theorem codeAt_sub_72 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 72)) sub_72 :=
  h.1 72 sub_72 (by decide +kernel) (by decide)
theorem codeAt_sub_73 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 73)) sub_73 :=
  h.1 73 sub_73 (by decide +kernel) (by decide)
theorem codeAt_sub_76 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 76)) sub_76 :=
  h.1 76 sub_76 (by decide +kernel) (by decide)
theorem codeAt_sub_77 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 77)) sub_77 :=
  h.1 77 sub_77 (by decide +kernel) (by decide)
theorem codeAt_sub_78 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 78)) sub_78 :=
  h.1 78 sub_78 (by decide +kernel) (by decide)
theorem codeAt_sub_79 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 79)) sub_79 :=
  h.1 79 sub_79 (by decide +kernel) (by decide)
/-- Campaign T51: the keygen's leaf-slot words (offsets 80..82). -/
theorem codeAt_sub80K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 80)) sub80K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub82K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 82)) sub82K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_83 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 83)) sub_83 :=
  h.1 83 sub_83 (by decide +kernel) (by decide)
theorem codeAt_sub_92 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 92)) sub_92 :=
  h.1 92 sub_92 (by decide +kernel) (by decide)
theorem codeAt_sub_95 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 95)) sub_95 :=
  h.1 95 sub_95 (by decide +kernel) (by decide)
theorem codeAt_sub96K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 96)) sub96K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_105 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 105)) sub_105 :=
  h.1 105 sub_105 (by decide +kernel) (by decide)
theorem codeAt_sub106K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 106)) sub106K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_112 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 112)) sub_112 :=
  h.1 112 sub_112 (by decide +kernel) (by decide)
theorem codeAt_sub_116 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 116)) sub_116 :=
  h.1 116 sub_116 (by decide +kernel) (by decide)
theorem codeAt_sub_117 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 117)) sub_117 :=
  h.1 117 sub_117 (by decide +kernel) (by decide)
theorem codeAt_sub_118 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 118)) sub_118 :=
  h.1 118 sub_118 (by decide +kernel) (by decide)
theorem codeAt_sub120K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 120)) sub120K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub140K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 140)) sub140K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_146 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 146)) sub_146 :=
  h.1 146 sub_146 (by decide +kernel) (by decide)
theorem codeAt_sub147K {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 147)) sub147K :=
  codeAt_kSub h (by decide +kernel)
theorem codeAt_sub_159 {image : Image} {b : Nat} (h : SubAt image b) :
    CodeAt image (pcOf (b + 159)) sub_159 :=
  h.1 159 sub_159 (by decide +kernel) (by decide)
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 100
sym_block blk_26 := symRun { noAlias := true } seg_26 (pcOf 26) 100
sym_block blk_28 := symRun { noAlias := true } seg_28 (pcOf 28) 100
sym_block blk_34 := symRun { noAlias := true } seg_34 (pcOf 34) 100
sym_block blk_36 := symRun { noAlias := true } seg_36 (pcOf 36) 100
sym_block blk_39 := symRun { noAlias := true } seg_39 (pcOf 39) 100
sym_block blk_48 := symRun { noAlias := true } seg_48 (pcOf 48) 100
sym_block blk_50 := symRun { noAlias := true } seg_50 (pcOf 50) 100
sym_block blk_51 := symRun { noAlias := true } seg_51 (pcOf 51) 100
sym_block blk_52 := symRun { noAlias := true } seg_52 (pcOf 52) 100
sym_block blk_65 := symRun { noAlias := true } seg_65 (pcOf 65) 100
sym_block blk_81 := symRun { noAlias := true } seg_81 (pcOf 81) 100
sym_block blk_84 := symRun { noAlias := true } seg_84 (pcOf 84) 100
sym_block blk_114 := symRun { noAlias := true } seg_114 (pcOf 114) 100
sym_block blk_277 := symRun { noAlias := true } seg_277 (pcOf 277) 100
sym_block blk_289 := symRun { noAlias := true } seg_289 (pcOf 289) 100
sym_block blk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 100
sym_block blk_310 := symRun { noAlias := true } seg_310 (pcOf 310) 100
sym_block blk_330 := symRun { noAlias := true } seg_330 (pcOf 330) 100
sym_block blk117_0 := symRun { noAlias := true } sub_0 (pcOf (117 + 0)) 100
sym_block blk1013_0 := symRun { noAlias := true } sub_0 (pcOf (1013 + 0)) 100
sym_block blk117_1 := symRun { noAlias := true } sub_1 (pcOf (117 + 1)) 100
sym_block blk1013_1 := symRun { noAlias := true } sub_1 (pcOf (1013 + 1)) 100
sym_block blk117_2 := symRun { noAlias := true } sub_2 (pcOf (117 + 2)) 100
sym_block blk1013_2 := symRun { noAlias := true } sub_2 (pcOf (1013 + 2)) 100
sym_block blk117_8 := symRun { noAlias := true } sub_8 (pcOf (117 + 8)) 100
sym_block blk1013_8 := symRun { noAlias := true } sub_8 (pcOf (1013 + 8)) 100
sym_block blk117_9 := symRun { noAlias := true } sub_9 (pcOf (117 + 9)) 100
sym_block blk1013_9 := symRun { noAlias := true } sub_9 (pcOf (1013 + 9)) 100
sym_block blk117_24 := symRun { noAlias := true } sub_24 (pcOf (117 + 24)) 100
sym_block blk1013_24 := symRun { noAlias := true } sub_24 (pcOf (1013 + 24)) 100
sym_block blk117_26 := symRun { noAlias := true } sub_26 (pcOf (117 + 26)) 100
sym_block blk1013_26 := symRun { noAlias := true } sub_26 (pcOf (1013 + 26)) 100
sym_block blk117_27 := symRun { noAlias := true } sub_27 (pcOf (117 + 27)) 100
sym_block blk1013_27 := symRun { noAlias := true } sub_27 (pcOf (1013 + 27)) 100
sym_block blk117_41 := symRun { noAlias := true } sub_41 (pcOf (117 + 41)) 100
sym_block blk1013_41 := symRun { noAlias := true } sub_41 (pcOf (1013 + 41)) 100
sym_block blk117_42 := symRun { noAlias := true } sub_42 (pcOf (117 + 42)) 100
sym_block blk1013_42 := symRun { noAlias := true } sub_42 (pcOf (1013 + 42)) 100
sym_block blk117_44 := symRun { noAlias := true } sub_44 (pcOf (117 + 44)) 100
sym_block blk1013_44 := symRun { noAlias := true } sub_44 (pcOf (1013 + 44)) 100
sym_block blk117_60 := symRun { noAlias := true } sub_60 (pcOf (117 + 60)) 100
sym_block blk1013_60 := symRun { noAlias := true } sub_60 (pcOf (1013 + 60)) 100
sym_block blk117_73 := symRun { noAlias := true } sub_73 (pcOf (117 + 73)) 100
sym_block blk1013_73 := symRun { noAlias := true } sub_73 (pcOf (1013 + 73)) 100
sym_block blk117_75 := symRun { noAlias := true } sub_75 (pcOf (117 + 75)) 100
sym_block blk1013_75 := symRun { noAlias := true } sub_75 (pcOf (1013 + 75)) 100
sym_block blk117_76 := symRun { noAlias := true } sub_76 (pcOf (117 + 76)) 100
sym_block blk1013_76 := symRun { noAlias := true } sub_76 (pcOf (1013 + 76)) 100
sym_block blk117_77 := symRun { noAlias := true } sub_77 (pcOf (117 + 77)) 100
sym_block blk1013_77 := symRun { noAlias := true } sub_77 (pcOf (1013 + 77)) 100
sym_block blk117_78 := symRun { noAlias := true } sub_78 (pcOf (117 + 78)) 100
sym_block blk1013_78 := symRun { noAlias := true } sub_78 (pcOf (1013 + 78)) 100
sym_block blk117_79 := symRun { noAlias := true } sub_79 (pcOf (117 + 79)) 100
sym_block blk1013_79 := symRun { noAlias := true } sub_79 (pcOf (1013 + 79)) 100
sym_block blk117_80 := symRun { noAlias := true } sub_80 (pcOf (117 + 80)) 100
sym_block blk1013_80 := symRun { noAlias := true } sub_80 (pcOf (1013 + 80)) 100
sym_block blk117_82 := symRun { noAlias := true } sub_82 (pcOf (117 + 82)) 100
sym_block blk1013_82 := symRun { noAlias := true } sub_82 (pcOf (1013 + 82)) 100
sym_block blk117_83 := symRun { noAlias := true } sub_83 (pcOf (117 + 83)) 100
sym_block blk1013_83 := symRun { noAlias := true } sub_83 (pcOf (1013 + 83)) 100
sym_block blk117_92 := symRun { noAlias := true } sub_92 (pcOf (117 + 92)) 100
sym_block blk1013_92 := symRun { noAlias := true } sub_92 (pcOf (1013 + 92)) 100
sym_block blk117_95 := symRun { noAlias := true } sub_95 (pcOf (117 + 95)) 100
sym_block blk1013_95 := symRun { noAlias := true } sub_95 (pcOf (1013 + 95)) 100
sym_block blk117_96 := symRun { noAlias := true } sub_96 (pcOf (117 + 96)) 100
sym_block blk1013_96 := symRun { noAlias := true } sub_96 (pcOf (1013 + 96)) 100
sym_block blk117_106 := symRun { noAlias := true } sub_106 (pcOf (117 + 106)) 100
sym_block blk1013_106 := symRun { noAlias := true } sub_106 (pcOf (1013 + 106)) 100
sym_block blk117_112 := symRun { noAlias := true } sub_112 (pcOf (117 + 112)) 100
sym_block blk1013_112 := symRun { noAlias := true } sub_112 (pcOf (1013 + 112)) 100
sym_block blk117_113 := symRun { noAlias := true } sub_113 (pcOf (117 + 113)) 100
sym_block blk1013_113 := symRun { noAlias := true } sub_113 (pcOf (1013 + 113)) 100
sym_block blk117_116 := symRun { noAlias := true } sub_116 (pcOf (117 + 116)) 100
sym_block blk1013_116 := symRun { noAlias := true } sub_116 (pcOf (1013 + 116)) 100
sym_block blk117_117 := symRun { noAlias := true } sub_117 (pcOf (117 + 117)) 100
sym_block blk1013_117 := symRun { noAlias := true } sub_117 (pcOf (1013 + 117)) 100
sym_block blk117_118 := symRun { noAlias := true } sub_118 (pcOf (117 + 118)) 100
sym_block blk1013_118 := symRun { noAlias := true } sub_118 (pcOf (1013 + 118)) 100
sym_block blk117_120 := symRun { noAlias := true } sub_120 (pcOf (117 + 120)) 100
sym_block blk1013_120 := symRun { noAlias := true } sub_120 (pcOf (1013 + 120)) 100
sym_block blk117_140 := symRun { noAlias := true } sub_140 (pcOf (117 + 140)) 100
sym_block blk1013_140 := symRun { noAlias := true } sub_140 (pcOf (1013 + 140)) 100
sym_block blk117_rev := symRun { noAlias := true } revCode (pcOf (117 + 1004)) 100
sym_block blk1013_rev := symRun { noAlias := true } revCode (pcOf (1013 + 1004)) 100
sym_block blk117_147 := symRun { noAlias := true } sub_147 (pcOf (117 + 147)) 100
sym_block kblk_96 := symRun { noAlias := true } sub96K (pcOf (117 + 96)) 100
sym_block kblk_80 := symRun { noAlias := true } sub80K (pcOf (117 + 80)) 100
sym_block kblk_82 := symRun { noAlias := true } sub82K (pcOf (117 + 82)) 100
sym_block kblk_106 := symRun { noAlias := true } sub106K (pcOf (117 + 106)) 100
sym_block kblk_120 := symRun { noAlias := true } sub120K (pcOf (117 + 120)) 100
sym_block kblk_140 := symRun { noAlias := true } sub140K (pcOf (117 + 140)) 100
sym_block blk1013_147 := symRun { noAlias := true } sub_147 (pcOf (1013 + 147)) 100
sym_block blk117_157 := symRun { noAlias := true } sub_157 (pcOf (117 + 157)) 100
sym_block blk1013_157 := symRun { noAlias := true } sub_157 (pcOf (1013 + 157)) 100
sym_block blk117_159 := symRun { noAlias := true } sub_159 (pcOf (117 + 159)) 100
sym_block blk1013_159 := symRun { noAlias := true } sub_159 (pcOf (1013 + 159)) 100
def st_0 : SymState := blk117_0.res.st
def pcE_0 (b : Nat) : E := .c (pcOf (b + 1))
theorem run_0 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_0 (pcOf (b + 0)) 100 =
      some ⟨st_0, pcE_0 b, blk117_0.res.stop, blk117_0.res.steps, blk117_0.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_0.trans (congrArg some (by kernel_rfl))
  · exact blk1013_0.trans (congrArg some (by kernel_rfl))
def st_1 : SymState := blk117_1.res.st
def pcE_1 (b : Nat) : E := rebase blk117_1.res.pc (pcOf (b + 8)) (pcOf (b + 2))
theorem run_1 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_1 (pcOf (b + 1)) 100 =
      some ⟨st_1, pcE_1 b, blk117_1.res.stop, blk117_1.res.steps, blk117_1.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_1.trans (congrArg some (by kernel_rfl))
  · exact blk1013_1.trans (congrArg some (by kernel_rfl))
def st_2 : SymState := blk117_2.res.st
def pcE_2 (b : Nat) : E := .c (pcOf (b + 8))
theorem run_2 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_2 (pcOf (b + 2)) 100 =
      some ⟨st_2, pcE_2 b, blk117_2.res.stop, blk117_2.res.steps, blk117_2.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_2.trans (congrArg some (by kernel_rfl))
  · exact blk1013_2.trans (congrArg some (by kernel_rfl))
def st_8 : SymState := blk117_8.res.st
def pcE_8 (b : Nat) : E := rebase blk117_8.res.pc (pcOf (b + 26)) (pcOf (b + 9))
theorem run_8 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_8 (pcOf (b + 8)) 100 =
      some ⟨st_8, pcE_8 b, blk117_8.res.stop, blk117_8.res.steps, blk117_8.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_8.trans (congrArg some (by kernel_rfl))
  · exact blk1013_8.trans (congrArg some (by kernel_rfl))
def st_9 : SymState := blk117_9.res.st
def pcE_9 (b : Nat) : E := .c (pcOf (b + 470))
theorem run_9 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_9 (pcOf (b + 9)) 100 =
      some ⟨st_9, pcE_9 b, blk117_9.res.stop, blk117_9.res.steps, blk117_9.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_9.trans (congrArg some (by kernel_rfl))
  · exact blk1013_9.trans (congrArg some (by kernel_rfl))
def st_24 : SymState := blk117_24.res.st
def pcE_24 (b : Nat) : E := .c (pcOf (b + 1))
theorem run_24 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_24 (pcOf (b + 24)) 100 =
      some ⟨st_24, pcE_24 b, blk117_24.res.stop, blk117_24.res.steps, blk117_24.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_24.trans (congrArg some (by kernel_rfl))
  · exact blk1013_24.trans (congrArg some (by kernel_rfl))
def st_26 : SymState := blk117_26.res.st
def pcE_26 (b : Nat) : E := blk117_26.res.pc
theorem run_26 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_26 (pcOf (b + 26)) 100 =
      some ⟨st_26, pcE_26 b, blk117_26.res.stop, blk117_26.res.steps, blk117_26.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_26.trans (congrArg some (by kernel_rfl))
  · exact blk1013_26.trans (congrArg some (by kernel_rfl))
def st_27 : SymState := blk117_27.res.st
def pcE_27 (b : Nat) : E := .c (pcOf (b + 41))
theorem run_27 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_27 (pcOf (b + 27)) 100 =
      some ⟨st_27, pcE_27 b, blk117_27.res.stop, blk117_27.res.steps, blk117_27.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_27.trans (congrArg some (by kernel_rfl))
  · exact blk1013_27.trans (congrArg some (by kernel_rfl))
def st_41 : SymState := blk117_41.res.st
def pcE_41 (b : Nat) : E := rebase blk117_41.res.pc (pcOf (b + 95)) (pcOf (b + 42))
theorem run_41 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_41 (pcOf (b + 41)) 100 =
      some ⟨st_41, pcE_41 b, blk117_41.res.stop, blk117_41.res.steps, blk117_41.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_41.trans (congrArg some (by kernel_rfl))
  · exact blk1013_41.trans (congrArg some (by kernel_rfl))
def st_42 : SymState := blk117_42.res.st
def pcE_42 (b : Nat) : E := rebase blk117_42.res.pc (pcOf (b + 60)) (pcOf (b + 44))
theorem run_42 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_42 (pcOf (b + 42)) 100 =
      some ⟨st_42, pcE_42 b, blk117_42.res.stop, blk117_42.res.steps, blk117_42.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_42.trans (congrArg some (by kernel_rfl))
  · exact blk1013_42.trans (congrArg some (by kernel_rfl))
def st_44 : SymState := blk117_44.res.st
def pcE_44 (b : Nat) : E := .c (pcOf (b + 59))
theorem run_44 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_44 (pcOf (b + 44)) 100 =
      some ⟨st_44, pcE_44 b, blk117_44.res.stop, blk117_44.res.steps, blk117_44.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_44.trans (congrArg some (by kernel_rfl))
  · exact blk1013_44.trans (congrArg some (by kernel_rfl))
def st_60 : SymState := blk117_60.res.st
def pcE_60 (b : Nat) : E := .c (pcOf (b + 72))
theorem run_60 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_60 (pcOf (b + 60)) 100 =
      some ⟨st_60, pcE_60 b, blk117_60.res.stop, blk117_60.res.steps, blk117_60.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_60.trans (congrArg some (by kernel_rfl))
  · exact blk1013_60.trans (congrArg some (by kernel_rfl))
def st_73 : SymState := blk117_73.res.st
def pcE_73 (b : Nat) : E := rebase blk117_73.res.pc (pcOf (b + 76)) (pcOf (b + 75))
theorem run_73 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_73 (pcOf (b + 73)) 100 =
      some ⟨st_73, pcE_73 b, blk117_73.res.stop, blk117_73.res.steps, blk117_73.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_73.trans (congrArg some (by kernel_rfl))
  · exact blk1013_73.trans (congrArg some (by kernel_rfl))
def st_75 : SymState := blk117_75.res.st
def pcE_75 (b : Nat) : E := .c (pcOf (b + 1000))
theorem run_75 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_75 (pcOf (b + 75)) 100 =
      some ⟨st_75, pcE_75 b, blk117_75.res.stop, blk117_75.res.steps, blk117_75.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_75.trans (congrArg some (by kernel_rfl))
  · exact blk1013_75.trans (congrArg some (by kernel_rfl))
def st_76 : SymState := blk117_76.res.st
def pcE_76 (b : Nat) : E := rebase blk117_76.res.pc (pcOf (b + 78)) (pcOf (b + 77))
theorem run_76 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_76 (pcOf (b + 76)) 100 =
      some ⟨st_76, pcE_76 b, blk117_76.res.stop, blk117_76.res.steps, blk117_76.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_76.trans (congrArg some (by kernel_rfl))
  · exact blk1013_76.trans (congrArg some (by kernel_rfl))
def st_77 : SymState := blk117_77.res.st
def pcE_77 (b : Nat) : E := .c (pcOf (b + 78))
theorem run_77 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_77 (pcOf (b + 77)) 100 =
      some ⟨st_77, pcE_77 b, blk117_77.res.stop, blk117_77.res.steps, blk117_77.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_77.trans (congrArg some (by kernel_rfl))
  · exact blk1013_77.trans (congrArg some (by kernel_rfl))
def st_78 (b : Nat) : SymState := { blk117_78.res.st with regs := blk117_78.res.st.regs.set Reg.x1 (.c (pcOf (b + 79))) }
def pcE_78 (b : Nat) : E := .c (pcOf (b + 0))
theorem run_78 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_78 (pcOf (b + 78)) 100 =
      some ⟨st_78 b, pcE_78 b, blk117_78.res.stop, blk117_78.res.steps, blk117_78.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_78.trans (congrArg some (by kernel_rfl))
  · exact blk1013_78.trans (congrArg some (by kernel_rfl))
def st_79 : SymState := blk117_79.res.st
def pcE_79 (b : Nat) : E := rebase blk117_79.res.pc (pcOf (b + 92)) (pcOf (b + 80))
theorem run_79 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_79 (pcOf (b + 79)) 100 =
      some ⟨st_79, pcE_79 b, blk117_79.res.stop, blk117_79.res.steps, blk117_79.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_79.trans (congrArg some (by kernel_rfl))
  · exact blk1013_79.trans (congrArg some (by kernel_rfl))
def st_80 : SymState := blk117_80.res.st
def pcE_80 (b : Nat) : E := .c (pcOf (b + 82))
theorem run_80 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_80 (pcOf (b + 80)) 100 =
      some ⟨st_80, pcE_80 b, blk117_80.res.stop, blk117_80.res.steps, blk117_80.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_80.trans (congrArg some (by kernel_rfl))
  · exact blk1013_80.trans (congrArg some (by kernel_rfl))
def st_82 : SymState := blk117_82.res.st
def pcE_82 (b : Nat) : E := .c (pcOf (b + 83))
theorem run_82 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_82 (pcOf (b + 82)) 100 =
      some ⟨st_82, pcE_82 b, blk117_82.res.stop, blk117_82.res.steps, blk117_82.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_82.trans (congrArg some (by kernel_rfl))
  · exact blk1013_82.trans (congrArg some (by kernel_rfl))
def st_83 : SymState := blk117_83.res.st
def pcE_83 (b : Nat) : E := .c (pcOf (b + 92))
theorem run_83 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_83 (pcOf (b + 83)) 100 =
      some ⟨st_83, pcE_83 b, blk117_83.res.stop, blk117_83.res.steps, blk117_83.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_83.trans (congrArg some (by kernel_rfl))
  · exact blk1013_83.trans (congrArg some (by kernel_rfl))
def st_92 : SymState := blk117_92.res.st
def pcE_92 (b : Nat) : E := .c (pcOf (b + 41))
theorem run_92 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_92 (pcOf (b + 92)) 100 =
      some ⟨st_92, pcE_92 b, blk117_92.res.stop, blk117_92.res.steps, blk117_92.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_92.trans (congrArg some (by kernel_rfl))
  · exact blk1013_92.trans (congrArg some (by kernel_rfl))
def st_95 : SymState := blk117_95.res.st
def pcE_95 (b : Nat) : E := rebase blk117_95.res.pc (pcOf (b + 112)) (pcOf (b + 96))
theorem run_95 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_95 (pcOf (b + 95)) 100 =
      some ⟨st_95, pcE_95 b, blk117_95.res.stop, blk117_95.res.steps, blk117_95.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_95.trans (congrArg some (by kernel_rfl))
  · exact blk1013_95.trans (congrArg some (by kernel_rfl))
def st_96 : SymState := blk117_96.res.st
def pcE_96 (b : Nat) : E := .c (pcOf (b + 105))
theorem run_96 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_96 (pcOf (b + 96)) 100 =
      some ⟨st_96, pcE_96 b, blk117_96.res.stop, blk117_96.res.steps, blk117_96.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_96.trans (congrArg some (by kernel_rfl))
  · exact blk1013_96.trans (congrArg some (by kernel_rfl))
def st_106 : SymState := blk117_106.res.st
def pcE_106 (b : Nat) : E := .c (pcOf (b + 112))
theorem run_106 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_106 (pcOf (b + 106)) 100 =
      some ⟨st_106, pcE_106 b, blk117_106.res.stop, blk117_106.res.steps, blk117_106.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_106.trans (congrArg some (by kernel_rfl))
  · exact blk1013_106.trans (congrArg some (by kernel_rfl))
def st_112 : SymState := blk117_112.res.st
def pcE_112 (b : Nat) : E := blk117_112.res.pc
theorem run_112 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_112 (pcOf (b + 112)) 100 =
      some ⟨st_112, pcE_112 b, blk117_112.res.stop, blk117_112.res.steps, blk117_112.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_112.trans (congrArg some (by kernel_rfl))
  · exact blk1013_112.trans (congrArg some (by kernel_rfl))
def st_113 : SymState := blk117_113.res.st
def pcE_113 (b : Nat) : E := .c (pcOf (b + 116))
theorem run_113 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_113 (pcOf (b + 113)) 100 =
      some ⟨st_113, pcE_113 b, blk117_113.res.stop, blk117_113.res.steps, blk117_113.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_113.trans (congrArg some (by kernel_rfl))
  · exact blk1013_113.trans (congrArg some (by kernel_rfl))
def st_116 : SymState := blk117_116.res.st
def pcE_116 (b : Nat) : E := rebase blk117_116.res.pc (pcOf (b + 159)) (pcOf (b + 117))
theorem run_116 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_116 (pcOf (b + 116)) 100 =
      some ⟨st_116, pcE_116 b, blk117_116.res.stop, blk117_116.res.steps, blk117_116.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_116.trans (congrArg some (by kernel_rfl))
  · exact blk1013_116.trans (congrArg some (by kernel_rfl))
def st_117 : SymState := blk117_117.res.st
def pcE_117 (b : Nat) : E := .c (pcOf (b + 118))
theorem run_117 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_117 (pcOf (b + 117)) 100 =
      some ⟨st_117, pcE_117 b, blk117_117.res.stop, blk117_117.res.steps, blk117_117.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_117.trans (congrArg some (by kernel_rfl))
  · exact blk1013_117.trans (congrArg some (by kernel_rfl))
def st_118 : SymState := blk117_118.res.st
def pcE_118 (b : Nat) : E := rebase blk117_118.res.pc (pcOf (b + 157)) (pcOf (b + 120))
theorem run_118 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_118 (pcOf (b + 118)) 100 =
      some ⟨st_118, pcE_118 b, blk117_118.res.stop, blk117_118.res.steps, blk117_118.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_118.trans (congrArg some (by kernel_rfl))
  · exact blk1013_118.trans (congrArg some (by kernel_rfl))
def st_120 : SymState := blk117_120.res.st
def pcE_120 (b : Nat) : E := rebase blk117_120.res.pc (pcOf (b + 1004)) (pcOf (b + 140))
theorem run_120 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_120 (pcOf (b + 120)) 100 =
      some ⟨st_120, pcE_120 b, blk117_120.res.stop, blk117_120.res.steps, blk117_120.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_120.trans (congrArg some (by kernel_rfl))
  · exact blk1013_120.trans (congrArg some (by kernel_rfl))
def st_140 : SymState := blk117_140.res.st
def pcE_140 (b : Nat) : E := .c (pcOf (b + 146))
theorem run_140 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_140 (pcOf (b + 140)) 100 =
      some ⟨st_140, pcE_140 b, blk117_140.res.stop, blk117_140.res.steps, blk117_140.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_140.trans (congrArg some (by kernel_rfl))
  · exact blk1013_140.trans (congrArg some (by kernel_rfl))
def st_rev : SymState := blk117_rev.res.st
def pcE_rev (b : Nat) : E := .c (pcOf (b + 140))
theorem run_rev {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } revCode (pcOf (b + 1004)) 100 =
      some ⟨st_rev, pcE_rev b, blk117_rev.res.stop, blk117_rev.res.steps, blk117_rev.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_rev.trans (congrArg some (by kernel_rfl))
  · exact blk1013_rev.trans (congrArg some (by kernel_rfl))
def st_147 : SymState := blk117_147.res.st
def pcE_147 (b : Nat) : E := .c (pcOf (b + 118))
theorem run_147 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_147 (pcOf (b + 147)) 100 =
      some ⟨st_147, pcE_147 b, blk117_147.res.stop, blk117_147.res.steps, blk117_147.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_147.trans (congrArg some (by kernel_rfl))
  · exact blk1013_147.trans (congrArg some (by kernel_rfl))
def st_157 : SymState := blk117_157.res.st
def pcE_157 (b : Nat) : E := .c (pcOf (b + 116))
theorem run_157 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_157 (pcOf (b + 157)) 100 =
      some ⟨st_157, pcE_157 b, blk117_157.res.stop, blk117_157.res.steps, blk117_157.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_157.trans (congrArg some (by kernel_rfl))
  · exact blk1013_157.trans (congrArg some (by kernel_rfl))
def st_159 : SymState := blk117_159.res.st
def pcE_159 (b : Nat) : E := blk117_159.res.pc
theorem run_159 {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } sub_159 (pcOf (b + 159)) 100 =
      some ⟨st_159, pcE_159 b, blk117_159.res.stop, blk117_159.res.steps, blk117_159.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact blk117_159.trans (congrArg some (by kernel_rfl))
  · exact blk1013_159.trans (congrArg some (by kernel_rfl))
sym_block max117Low := symRun { noAlias := true } maxLow (pcOf (117 + 1000)) 100
sym_block max1013Low := symRun { noAlias := true } maxLow (pcOf (1013 + 1000)) 100
sym_block max117High := symRun { noAlias := true } maxHigh (pcOf (117 + 1002)) 100
sym_block max1013High := symRun { noAlias := true } maxHigh (pcOf (1013 + 1002)) 100
def maxLowState : SymState := max117Low.res.st
def maxLowPC (b : Nat) : E := rebase max117Low.res.pc (pcOf (b + 76)) (pcOf (b + 1002))
theorem run_maxLow {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } maxLow (pcOf (b + 1000)) 100 =
      some ⟨maxLowState, maxLowPC b, max117Low.res.stop, max117Low.res.steps, max117Low.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact max117Low.trans (congrArg some (by kernel_rfl))
  · exact max1013Low.trans (congrArg some (by kernel_rfl))
def maxHighState : SymState := max117High.res.st
def maxHighPC (b : Nat) : E := .c (pcOf (b + 76))
theorem run_maxHigh {b : Nat} (hb : b = 117 ∨ b = 1013) :
    symRun { noAlias := true } maxHigh (pcOf (b + 1002)) 100 =
      some ⟨maxHighState, maxHighPC b, max117High.res.stop, max117High.res.steps, max117High.res.cycles⟩ := by
  rcases hb with rfl | rfl
  · exact max117High.trans (congrArg some (by kernel_rfl))
  · exact max1013High.trans (congrArg some (by kernel_rfl))
/-! C4: the keygen-only runs (`b = 117` is forced by `SubAt`). -/
def st_80K : SymState := kblk_80.res.st
theorem run_80K : symRun { noAlias := true } sub80K (pcOf (117 + 80)) 100 =
    some ⟨st_80K, .c (pcOf (117 + 82)), kblk_80.res.stop, kblk_80.res.steps, kblk_80.res.cycles⟩ :=
  kblk_80.trans (congrArg some (by kernel_rfl))
def st_82K : SymState := kblk_82.res.st
theorem run_82K : symRun { noAlias := true } sub82K (pcOf (117 + 82)) 100 =
    some ⟨st_82K, .c (pcOf (117 + 83)), kblk_82.res.stop, kblk_82.res.steps, kblk_82.res.cycles⟩ :=
  kblk_82.trans (congrArg some (by kernel_rfl))
def st_96K : SymState := kblk_96.res.st
theorem run_96K : symRun { noAlias := true } sub96K (pcOf (117 + 96)) 100 =
    some ⟨st_96K, .c (pcOf (117 + 105)), kblk_96.res.stop, kblk_96.res.steps, kblk_96.res.cycles⟩ :=
  kblk_96.trans (congrArg some (by kernel_rfl))
def st_106K : SymState := kblk_106.res.st
theorem run_106K : symRun { noAlias := true } sub106K (pcOf (117 + 106)) 100 =
    some ⟨st_106K, .c (pcOf (117 + 112)), kblk_106.res.stop, kblk_106.res.steps, kblk_106.res.cycles⟩ :=
  kblk_106.trans (congrArg some (by kernel_rfl))
def st_120K : SymState := kblk_120.res.st
theorem run_120K : symRun { noAlias := true } sub120K (pcOf (117 + 120)) 100 =
    some ⟨st_120K, .c (pcOf (117 + 140)), kblk_120.res.stop, kblk_120.res.steps, kblk_120.res.cycles⟩ :=
  kblk_120.trans (congrArg some (by kernel_rfl))
def st_140K : SymState := kblk_140.res.st
theorem run_140K : symRun { noAlias := true } sub140K (pcOf (117 + 140)) 100 =
    some ⟨st_140K, .c (pcOf (117 + 146)), kblk_140.res.stop, kblk_140.res.steps, kblk_140.res.cycles⟩ :=
  kblk_140.trans (congrArg some (by kernel_rfl))
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_PackedShared ====
section

section
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Pairing stage 1: the sign chain header now ends at 1031 (`jal 1732`, the G/F step block), with `t3 = CHAIN`
and no HASH arguments set. -/
structure SignHeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  x28 : t.getReg .x28 = BitVec.ofNat 64 0x201A0
  regs : RegsExcept s t [.x6, .x7, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)
theorem sign_header_0 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps Images.signReferenceImage s 25 25 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 12 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_body.res.toState s1
  have h2 := steps_sign_body s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_store.res.toState s2
  have h3 := steps_sign_store s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_body.res, rv_simp, h8])
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
theorem sign_header_1 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps Images.signReferenceImage s 28 28 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 7 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_inc.res.toState s2
  have h3 := steps_sign_inc s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_inc.res, run_sign_body.res, rv_simp, h8])
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
theorem sign_header_2 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps Images.signReferenceImage s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
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
theorem sign_header_3 (s : MachineState) (hpc : s.pc = pcOf 1022)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps Images.signReferenceImage s 29 29 t ∧ t.pc = pcOf 1031 ∧ SignHeaderPost s t 6 := by
  let s0 := run_sign_entry.res.toState s
  have h0 := steps_sign_entry s hpc
  let s1 := run_sign_layer0.res.toState s0
  have h1 := steps_sign_layer0 s0 (by simp [s0, run_sign_entry.res, rv_simp, h8])
  let s2 := run_sign_layer1.res.toState s1
  have h2 := steps_sign_layer1 s1 (by simp [s0, s1, run_sign_entry.res, run_sign_layer0.res, rv_simp, h8])
  let s3 := run_sign_layer23.res.toState s2
  have h3 := steps_sign_layer23 s2 (by simp [s0, s1, s2, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, rv_simp, h8])
  let s4 := run_sign_body.res.toState s3
  have h4 := steps_sign_body s3 (by simp [s0, s1, s2, s3, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, rv_simp, h8])
  let s5 := run_sign_store.res.toState s4
  have h5 := steps_sign_store s4 (by simp [s0, s1, s2, s3, s4, run_sign_entry.res, run_sign_layer0.res, run_sign_layer1.res, run_sign_layer23.res, run_sign_body.res, rv_simp, h8])
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
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
section
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem keygen_header_1 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps Images.keygenImage s 28 28 t ∧ t.pc = pcOf 135 ∧ HeaderPost s t 7 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_inc.res.toState s2
  have h3 := steps_keygen_inc s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_inc.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem keygen_header_2 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps Images.keygenImage s 29 29 t ∧ t.pc = pcOf 135 ∧ HeaderPost s t 6 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_layer23.res.toState s2
  have h3 := steps_keygen_layer23 s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem keygen_header_3 (s : MachineState) (hpc : s.pc = pcOf 126)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps Images.keygenImage s 29 29 t ∧ t.pc = pcOf 135 ∧ HeaderPost s t 6 := by
  let s0 := run_keygen_entry.res.toState s
  have h0 := steps_keygen_entry s hpc
  let s1 := run_keygen_layer0.res.toState s0
  have h1 := steps_keygen_layer0 s0 (by simp [s0, run_keygen_entry.res, rv_simp, h8])
  let s2 := run_keygen_layer1.res.toState s1
  have h2 := steps_keygen_layer1 s1 (by simp [s0, s1, run_keygen_entry.res, run_keygen_layer0.res, rv_simp, h8])
  let s3 := run_keygen_layer23.res.toState s2
  have h3 := steps_keygen_layer23 s2 (by simp [s0, s1, s2, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, rv_simp, h8])
  let s4 := run_keygen_body.res.toState s3
  have h4 := steps_keygen_body s3 (by simp [s0, s1, s2, s3, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, rv_simp, h8])
  let s5 := run_keygen_store.res.toState s4
  have h5 := steps_keygen_store s4 (by simp [s0, s1, s2, s3, s4, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_keygen_entry.res, run_keygen_layer0.res, run_keygen_layer1.res, run_keygen_layer23.res, run_keygen_body.res, run_keygen_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
section
namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
set_option backward.isDefEq.respectTransparency false
theorem routedAt_nat (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) = BitVec.ofNat 64 (tree * 2 ^ height lay + leaf) := by
  rw [routedAt, ht, hf, ofNat_shl, ofNat_add_ofNat]
theorem routedAt_high_zero (s : MachineState) (lay : Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31)
    (ht : s.getReg .x9 = BitVec.ofNat 64 tree)
    (hf : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    routedAt s (height lay) >>> 32 = 0 := by
  rw [routedAt_nat s lay tree leaf ht hf, ofNat_shr _ _ (by omega),
    Nat.div_eq_of_lt (by omega)]
  rfl
theorem packedAt_nat (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = BitVec.ofNat 64
      (128 + i + step * 2^8 + (tree * 2^height lay + leaf) * 2^16 + lay.val * 2^48 + 193 * 2^56) := by
  have hl := lay.isLt
  have hm : BitVec.ofNat 64 step &&& 255#64 = BitVec.ofNat 64 step := by
    interval_cases step <;> rfl
  have hroute : ((BitVec.ofNat 64 (tree * 2^height lay + leaf) <<< 32) >>> 16) =
      BitVec.ofNat 64 ((tree * 2^height lay + leaf) * 2^16) := by
    rw [ofNat_shl, ofNat_shr _ _ (by omega)]
    congr 1
    omega
  rw [packedAt, routedAt_nat s lay tree leaf h9 h18, hroute, h8, h19, h20, hm,
    ofNat_shl, ofNat_shl, ofNat_shl]
  rw [ofNat_or_disjoint' i 128 7 (by omega) (by decide)]
  rw [ofNat_or_disjoint' _ _ 48 (by omega) (by omega)]
  rw [ofNat_or_disjoint' _ _ 56 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 16 (by omega) (by omega)]
  rw [ofNat_or_disjoint _ _ 8 (by omega) (by omega)]
  congr 1
  omega
private theorem low_ofNat (n : Nat) :
    (BitVec.ofNat 128 n).extractLsb' 0 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
  omega
theorem packedAt_source (s : MachineState) (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 step) :
    packedAt s (height lay) = (chainHeader lay tree leaf i step).extractLsb' 0 64 := by
  exact (packedAt_nat s lay tree leaf i step hr hi hs h8 h9 h18 h19 h20).trans
    ((congrArg (fun x : BitVec 128 => x.extractLsb' 0 64)
      (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (low_ofNat _)).symm
private theorem high_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 128 n).extractLsb' 64 64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]
  change _ = 0
  omega
theorem source_high_actual (lay : Layer) (tree leaf i step : Nat)
    (hr : tree * 2 ^ height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ height lay)
    (hi : i < 64) (hs : step < 8) :
    (chainHeader lay tree leaf i step).extractLsb' 64 64 = 0#64 := by
  have hl := lay.isLt
  exact (congrArg (fun x : BitVec 128 => x.extractLsb' 64 64)
    (chainHeader_actual lay tree leaf i step hr hf hi hs)).trans (high_ofNat _ (by omega))
end SigGolfCandidate.T3M.Keygen.PackedBlocks
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3
open PackedBlocks
set_option backward.isDefEq.respectTransparency false
def headerK (lay : Layer) : Nat := if lay.val = 0 then 30 else if lay.val = 1 then 33 else 34
def rungK (lay : Layer) : Nat := headerK lay + 5
def rungC (lay : Layer) : Nat := headerK lay + 12
theorem shared_header {image : Image} {b : Nat} (h : SubAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (b + 9)) (lay : Layer)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) :
    ∃ t, Steps image s (headerK lay - 5) (headerK lay - 5) t ∧ t.pc = pcOf (b + 18) ∧
      HeaderPost s t (height lay) := by
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  fin_cases lay
  · exact keygen_header_0 s hpc h8
  · exact keygen_header_1 s hpc h8
  · exact keygen_header_2 s hpc h8
  · exact keygen_header_3 s hpc h8
theorem shared_header_source {image : Image} {b : Nat} (h : SubAt image b)
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
end SigGolfCandidate.T3M.Keygen
end
end
-- ==== merged from T3M_Keygen_KPair ====
section

/-! # Witness stack (charge 86): the keygen chain step block (top G/F)

The keygen chain routine at 117 ends its header at 134 (`sd t1,16(t3)` with `t3 = CHAIN`); 135 jumps to the step block
at 689:

* G path (`s0 = 0`, `s3` even, `s3 ≤ 52`): copy the header words `CHAIN+16/24` to `CHAIN+64/72`, zero
  `CHAIN+80 .. CHAIN+112`, hash the 64 bytes at `CHAIN+48` (`value | header | 0 | 0`) to `CHAIN+32` (interior steps:
  the HIGH half lands in the value slot) or to `CHAIN+48` (the terminal step `maxDigit 0 i - 1`: the low half), then
  `jal 141`.
* F path: zero `CHAIN+32 .. CHAIN+48`, hash the 64 bytes at `CHAIN` to `CHAIN+48`, then `jal 141`.

141/142 (`addi s4,s4,1; jal 118`) are the old tail. `kpair_rung` is the whole block from 135 as a `TSim` of
`T3.projHash (topChainHigh i m) (topChainInput leaf i m v)` (top tree, tree 0). -/

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput pad64 zero16 height chainHeader maxDigit topIsG topChainHigh
  topChainInput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

abbrev PRIV : Nat := 0x20000
abbrev SEEDS : Nat := 0x20040
abbrev CHAIN : Nat := 0x201A0
abbrev NODE : Nat := 0x20200
abbrev NOUT : Nat := 0x20240
abbrev LOUT : Nat := 0x203C0
abbrev LEAFPK : Nat := 0x20600
/-- Campaign T8D: the keygen top leaf's coefficient buffer (24 digests, COEFGEN/HORN). -/
abbrev KCOEF : Nat := 0x21000

local instance (image : Image) (pc : Word) (code : List (BitVec 32)) :
    Decidable (CodeAt image pc code) := by
  unfold CodeAt
  infer_instance

/-! ### The step block 135, 689..720 -/
def kJmp : List (BitVec 32) := [0x0a90006f]
def kSel0 : List (BitVec 32) := [0x06041263]
def kSel1 : List (BitVec 32) := [0x0019f313, 0x00000393, 0x04731c63]
def kSel2 : List (BitVec 32) := [0x03400393, 0x0533c863]
/-- Campaign T51: 706 `addi t1, s5, -1` (terminal step `maxDigit - 1`), 708 `bne s3, zero, 710`. -/
def kG : List (BitVec 32) := [0x010e3303, 0x046e3023, 0x018e3303, 0x046e3423, 0x040e3823, 0x040e3c23, 0x060e3023,
  0x060e3423, 0x030e0513, 0x04000593, 0x020e0613, 0xfffa8313, 0x03300393, 0x00099463]
/-- Campaign T51: 709 (chain 0 only) `mv t1, s5`: no terminal step, chain 0 keeps the HIGH half on every step. -/
def kG9 : List (BitVec 32) := [0x000a8313]
def kG10 : List (BitVec 32) := [0x006a1463]
def kG11 : List (BitVec 32) := [0x030e0613]
def kEcall : List (BitVec 32) := [0x00000073]
def kGt : List (BitVec 32) := [0xf10ff06f]
def kF : List (BitVec 32) := [0x020e3023, 0x020e3423, 0x000e0513, 0x04000593, 0x030e0613]
def kFt : List (BitVec 32) := [0xef4ff06f]
/-- The keygen step block (32 words at 689). -/
def kStepBlock : List (BitVec 32) := kSel0 ++ kSel1 ++ kSel2 ++ kG ++ kG9 ++ kG10 ++ kG11 ++ kEcall ++ kGt ++ kF ++
  kEcall ++ kFt
theorem kStepBlock_length : kStepBlock.length = 32 := by decide
sym_block bkJ := symRun { noAlias := true } kJmp (pcOf 135) 100
sym_block bkS0 := symRun { noAlias := true } kSel0 (pcOf 689) 100
sym_block bkS1 := symRun { noAlias := true } kSel1 (pcOf 690) 100
sym_block bkS2 := symRun { noAlias := true } kSel2 (pcOf 693) 100
sym_block bkG := symRun { noAlias := true } kG (pcOf 695) 100
sym_block bkG9 := symRun { noAlias := true } kG9 (pcOf 709) 100
sym_block bkG10 := symRun { noAlias := true } kG10 (pcOf 710) 100
sym_block bkG11 := symRun { noAlias := true } kG11 (pcOf 711) 100
sym_block bkGt := symRun { noAlias := true } kGt (pcOf 713) 100
sym_block bkF := symRun { noAlias := true } kF (pcOf 714) 100
sym_block bkFt := symRun { noAlias := true } kFt (pcOf 720) 100

theorem codeAt_kJ : CodeAt Images.keygenImage (pcOf 135) kJmp := by decide +kernel
theorem codeAt_kS0 : CodeAt Images.keygenImage (pcOf 689) kSel0 := by decide +kernel
theorem codeAt_kS1 : CodeAt Images.keygenImage (pcOf 690) kSel1 := by decide +kernel
theorem codeAt_kS2 : CodeAt Images.keygenImage (pcOf 693) kSel2 := by decide +kernel
theorem codeAt_kG : CodeAt Images.keygenImage (pcOf 695) kG := by decide +kernel
theorem codeAt_kG9 : CodeAt Images.keygenImage (pcOf 709) kG9 := by decide +kernel
theorem codeAt_kG10 : CodeAt Images.keygenImage (pcOf 710) kG10 := by decide +kernel
theorem codeAt_kG11 : CodeAt Images.keygenImage (pcOf 711) kG11 := by decide +kernel
theorem codeAt_kGcall : CodeAt Images.keygenImage (pcOf 712) kEcall := by decide +kernel
theorem codeAt_kGt : CodeAt Images.keygenImage (pcOf 713) kGt := by decide +kernel
theorem codeAt_kF : CodeAt Images.keygenImage (pcOf 714) kF := by decide +kernel
theorem codeAt_kFcall : CodeAt Images.keygenImage (pcOf 719) kEcall := by decide +kernel
theorem codeAt_kFt : CodeAt Images.keygenImage (pcOf 720) kFt := by decide +kernel

theorem kmd (i : Nat) : maxDigit 0 i = if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5 := by
  simp [maxDigit]
theorem kmd_pos (i : Nat) : 4 ≤ maxDigit 0 i ∧ maxDigit 0 i ≤ 6 := by rw [kmd]; split_ifs <;> omega
/-- Campaign T51: the LOW terminal step of a G chain (`m + 1 = maxDigit 0 i`), chain 0 excluded. -/
def kterm (i m : Nat) : Bool := decide (m + 1 = maxDigit 0 i) && decide (i ≠ 0)
theorem kne_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem kand1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

/-- Steps of the keygen step block after the header (jump, selection, body, HASH and `jal 141`, without the
`addi; jal` tail at 141): G `23 + [i = 0] + [terminal, i ≠ 0]`, F (odd chain) `11`. -/
def kgX (i m : Nat) : Nat :=
  if topIsG i then 23 + (if i = 0 then 1 else 0) + (if kterm i m then 1 else 0) else 11

/-- 135 `jal 689`, 689 `bne s0,zero,714` with `s0 = 0`, 690..692 `andi; addi; bne t1,t2,714`. -/
theorem ksel_spec (s : MachineState) (hpc : s.pc = pcOf 135) (i : Nat) (hi : i < 2 ^ 63)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps Images.keygenImage s 5 5 t ∧ t.pc = (if i % 2 = 0 then pcOf 693 else pcOf 714) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  have st0 := symRun_sound bkJ codeAt_kJ s hpc (by simp [bkJ.res, rv_simp])
  set u0 := bkJ.res.toState s with hu0
  have u0pc : u0.pc = pcOf 689 := by simp [hu0, bkJ.res, E.eval]
  have u0r : ∀ r, u0.getReg r = s.getReg r := by intro r; cases r <;> rfl
  have u0m : ∀ A, u0.getMem A = s.getMem A := by intro A; rfl
  have st1 := symRun_sound bkS0 codeAt_kS0 u0 u0pc (by simp [bkS0.res, rv_simp])
  set u1 := bkS0.res.toState u0 with hu1
  have u1pc : u1.pc = pcOf 690 := by
    simp only [hu1, Result.toState_pc, bkS0.res, E.eval, CmpOp.eval, u0r, h8]
    simp
  have u1r : ∀ r, u1.getReg r = s.getReg r := by
    intro r; rw [← u0r r]; cases r <;> simp [hu1, bkS0.res, rv_simp] <;> rfl
  have u1m : ∀ A, u1.getMem A = s.getMem A := by intro A; rw [← u0m A]; simp [hu1, bkS0.res, rv_simp]
  have st2 := symRun_sound bkS1 codeAt_kS1 u1 u1pc (by simp [bkS1.res, rv_simp])
  refine ⟨_, ((st0.trans st1).trans st2).of_eq (by simp [bkJ.res, bkS0.res, bkS1.res])
    (by simp [bkJ.res, bkS0.res, bkS1.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkS1.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, u1r, h19, kand1_ofNat]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, kne_of (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr
    rw [← u1r r]; cases r <;> simp_all [bkS1.res, rv_simp]
  · intro A _ _; rw [← u1m]; simp [bkS1.res, rv_simp]

/-- 693 `addi t2,zero,52`, 694 `blt t2,s3,714`. -/
theorem ksel2_spec (s : MachineState) (hpc : s.pc = pcOf 693) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps Images.keygenImage s 2 2 t ∧ t.pc = (if 52 < i then pcOf 714 else pcOf 695) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkS2 codeAt_kS2 s hpc (by simp [bkS2.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, bkS2.res, E.eval, CmpOp.eval, rv_simp, h19]
    rw [show (BitVec.ofNat 64 52 : Word) = BitVec.ofNat 64 52 from rfl, ofNat_slt 52 i (by norm_num) hi]
    by_cases h : 52 < i <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [bkS2.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkS2.res, rv_simp]

/-- The G body 695..711: header copy, pads, HASH arguments (output `CHAIN+48` on the terminal step). Campaign T51:
`t1 = maxDigit 0 i - 1` (706), chain 0 `t1 = maxDigit 0 i` (709), so chain 0 has no terminal step. -/
theorem kg_spec (s : MachineState) (hpc : s.pc = pcOf 695) (i m : Nat) (hi : i < 2 ^ 63) (hm : m < 2 ^ 63)
    (hmd : m < maxDigit 0 i)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h20 : s.getReg .x20 = BitVec.ofNat 64 m)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 (maxDigit 0 i))
    (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps Images.keygenImage s (15 + (if i = 0 then 1 else 0) + (if kterm i m then 1 else 0))
        (15 + (if i = 0 then 1 else 0) + (if kterm i m then 1 else 0)) t ∧ t.pc = pcOf 712 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if kterm i m then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hmdp := kmd_pos i
  have hobl : Oblig.all s bkG.res.st.obl := by
    simp only [bkG.res]
    t3n [h28, CHAIN]
    try norm_num
  have st := symRun_sound bkG codeAt_kG s hpc hobl
  set u := bkG.res.toState s with hu
  have upc : u.pc = (if i = 0 then pcOf 709 else pcOf 710) := by
    simp only [hu, Result.toState_pc, bkG.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 0
    · subst h; simp
    · have : BitVec.ofNat 64 i ≠ 0#64 := by
        rw [Ne, show (0#64) = BitVec.ofNat 64 0 from rfl, ofNat_inj (by omega) (by norm_num)]; exact h
      simp [h, this]
  have ur : RegsExcept s u [.x6, .x7, .x10, .x11, .x12] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, bkG.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    have hn' : ¬ (131552 ≤ A ∧ A < 131600) := by simpa [CHAIN] using hn
    simp only [hu, Result.toState_getMem, bkG.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (maxDigit 0 i - 1) := by
    simp only [hu, Result.toState_getReg, bkG.res, rv_simp, h21]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    omega
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, bkG.res, rv_simp, h28]; rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, bkG.res, rv_simp]
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, bkG.res, rv_simp, h28]; rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, bkG.res]
      t3n [h28, CHAIN]
  -- 709 (chain 0): t1 := s5 = maxDigit 0 0
  obtain ⟨v, kv, sv, hkv, vpc, v6, vr, vm⟩ : ∃ v kv, Steps Images.keygenImage u kv kv v ∧
      kv = (if i = 0 then 1 else 0) ∧ v.pc = pcOf 710 ∧
      v.getReg .x6 = BitVec.ofNat 64 (if i = 0 then maxDigit 0 i else maxDigit 0 i - 1) ∧ RegsExcept u v [.x6] ∧
      (∀ A, v.getMem A = u.getMem A) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at upc
      refine ⟨_, 1, symRun_sound bkG9 codeAt_kG9 u upc (by simp [bkG9.res, rv_simp]), by simp [h0],
        by simp [bkG9.res, E.eval], ?_, ?_, ?_⟩
      · rw [if_pos h0]
        simp only [Result.toState_getReg, bkG9.res, rv_simp]
        rw [ur.get (by simp), h21]
      · intro r hr; simp at hr; cases r <;> simp_all [bkG9.res, rv_simp] <;> rfl
      · intro A; simp [bkG9.res, rv_simp]
    · rw [if_neg h0] at upc
      refine ⟨u, 0, Steps.refl _, by simp [h0], upc, ?_, fun _ _ => rfl, fun _ => rfl⟩
      rw [u6, if_neg h0]
  have hmd' : (if i = 0 then maxDigit 0 i else maxDigit 0 i - 1) < 2 ^ 64 := by split <;> omega
  -- 710 `bne s4,t1,712`
  have stw := symRun_sound bkG10 codeAt_kG10 v vpc (by simp [bkG10.res, rv_simp])
  set w := bkG10.res.toState v with hw
  have v20 : v.getReg .x20 = BitVec.ofNat 64 m := by rw [vr.get (by simp), ur.get (by simp)]; exact h20
  have wpc : w.pc = (if kterm i m then pcOf 711 else pcOf 712) := by
    simp only [hw, Result.toState_pc, bkG10.res, E.eval, CmpOp.eval, v20, v6]
    rw [kne_of (by omega) hmd']
    have : (m ≠ if i = 0 then maxDigit 0 i else maxDigit 0 i - 1) ↔ ¬ (kterm i m = true) := by
      unfold kterm
      by_cases h0 : i = 0
      · subst h0; simp; omega
      · simp [h0]; omega
    by_cases h : kterm i m = true <;> simp_all
  have wr : ∀ r, w.getReg r = v.getReg r := by intro r; cases r <;> simp [hw, bkG10.res, rv_simp] <;> rfl
  have wm : ∀ A, w.getMem A = v.getMem A := by intro A; simp [hw, bkG10.res, rv_simp]
  have g : ∀ r, r ∉ [Reg.x6, .x7, .x10, .x11, .x12] → w.getReg r = s.getReg r := by
    intro r hr; rw [wr, vr.get (by simp at hr ⊢; tauto), ur.get hr]
  by_cases ht : kterm i m = true
  · rw [if_pos ht] at wpc
    have st11 := symRun_sound bkG11 codeAt_kG11 w wpc (by simp [bkG11.res, rv_simp])
    have xm : ∀ A, (bkG11.res.toState w).getMem A = w.getMem A := by intro A; simp [bkG11.res, rv_simp]
    have xr : RegsExcept w (bkG11.res.toState w) [.x12] := by
      intro r hr; simp at hr; cases r <;> simp_all [bkG11.res, rv_simp] <;> rfl
    have h28w : w.getReg .x28 = BitVec.ofNat 64 CHAIN := by rw [g _ (by simp)]; exact h28
    refine ⟨_, ((st.trans sv).trans (stw.trans st11)).of_eq (by simp [hkv, ht, bkG.res, bkG10.res, bkG11.res]; omega)
      (by simp [hkv, ht, bkG.res, bkG10.res, bkG11.res]; omega), by simp [bkG11.res, E.eval], ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [xr.get (by simp), wr, vr.get (by simp)]; exact u10
    · rw [xr.get (by simp), wr, vr.get (by simp)]; exact u11
    · rw [if_pos ht]; simp only [Result.toState_getReg, bkG11.res, rv_simp, h28w]; rfl
    all_goals (try rw [xm, wm, vm])
    · exact umem.1
    · exact umem.2.1
    · exact umem.2.2.1
    · exact umem.2.2.2.1
    · exact umem.2.2.2.2.1
    · exact umem.2.2.2.2.2
    · intro r hr; rw [xr.get (by simp at hr ⊢; tauto)]; exact g r hr
    · intro A hA hn; rw [xm, wm, vm]; exact uf A hA hn
  · rw [if_neg ht] at wpc
    refine ⟨w, ((st.trans sv).trans stw).of_eq (by simp [hkv, ht, bkG.res, bkG10.res]; omega)
      (by simp [hkv, ht, bkG.res, bkG10.res]; omega), wpc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [wr, vr.get (by simp)]; exact u10
    · rw [wr, vr.get (by simp)]; exact u11
    · rw [if_neg ht, wr, vr.get (by simp)]; exact u12
    all_goals (try rw [wm, vm])
    · exact umem.1
    · exact umem.2.1
    · exact umem.2.2.1
    · exact umem.2.2.2.1
    · exact umem.2.2.2.2.1
    · exact umem.2.2.2.2.2
    · exact g
    · intro A hA hn; rw [wm, vm]; exact uf A hA hn

/-- The F body 714..718: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem kf_spec (s : MachineState) (hpc : s.pc = pcOf 714) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps Images.keygenImage s 5 5 t ∧ t.pc = pcOf 719 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s bkF.res.st.obl := by
    simp only [bkF.res]
    t3n [h28, CHAIN]
    try norm_num
  refine ⟨_, symRun_sound bkF codeAt_kF s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [bkF.res, E.eval]
  · simp only [Result.toState_getReg, bkF.res, rv_simp, h28]
  · simp only [Result.toState_getReg, bkF.res, rv_simp]
  · simp only [Result.toState_getReg, bkF.res, rv_simp, h28]; rfl
  · simp only [Result.toState_getMem, bkF.res]; t3n [h28, CHAIN]
  · simp only [Result.toState_getMem, bkF.res]; t3n [h28, CHAIN]
  · intro r hr; simp at hr; cases r <;> simp_all [bkF.res, rv_simp] <;> rfl
  · intro A hA hn
    have hn' : ¬ (A = 131520 ∨ A = 131528) := by simpa [CHAIN] using hn
    simp only [Result.toState_getMem, bkF.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)

/-- 713 / 720 `jal 141`. -/
theorem ktail_spec (s : MachineState) (hpc : s.pc = pcOf 713 ∨ s.pc = pcOf 720) :
    ∃ t, Steps Images.keygenImage s 1 1 t ∧ t.pc = pcOf 141 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  rcases hpc with hpc | hpc
  · refine ⟨_, symRun_sound bkGt codeAt_kGt s hpc (by simp [bkGt.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [bkGt.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  · refine ⟨_, symRun_sound bkFt codeAt_kFt s hpc (by simp [bkFt.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [bkFt.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl

def kT24 : List (BitVec 32) := [1706515, 0xfa1ff06f]
sym_block bkT24 := symRun { noAlias := true } kT24 (pcOf 141) 100
theorem codeAt_kT24 : CodeAt Images.keygenImage (pcOf 141) kT24 := by decide +kernel
/-- 141 `addi s4,s4,1`, 142 `jal 118`. -/
theorem kt24_spec (s : MachineState) (hpc : s.pc = pcOf 141) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps Images.keygenImage s 2 2 t ∧ t.pc = pcOf (117 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound bkT24 codeAt_kT24 s hpc (by simp [bkT24.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [bkT24.res, E.eval]
  · simp only [Result.toState_getReg, bkT24.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [bkT24.res, rv_simp] <;> rfl
  · intro A _ _; simp [bkT24.res, rv_simp]

/-! ### The whole rung after the header -/
theorem wordsOf_topChainInput_G {i : Nat} (hG : topIsG i = true) (leaf step : Nat) (v : Digest) :
    wordsOf (topChainInput leaf i step v) =
      [v.extractLsb' 0 64, v.extractLsb' 64 64, (chainHeader 0 0 leaf i step).extractLsb' 0 64,
        (chainHeader 0 0 leaf i step).extractLsb' 64 64, 0, 0, 0, 0] := by
  unfold topChainInput; rw [if_pos hG]
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length, zero16]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_zero16, wordsOf_bytesLE16,
    wordsOf_bytesLE16]
  rfl
theorem topChainInput_length (leaf i step : Nat) (v : Digest) : (topChainInput leaf i step v).length = 64 := by
  unfold topChainInput; split <;> simp [chainInput, bytesLE_length, zero16]
theorem topChainInput_blocks (leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (topChainInput leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [topChainInput_length]),
    blocks_toQ ⟨by rw [topChainInput_length]; omega, by rw [topChainInput_length]⟩, topChainInput_length]
theorem topChainInput_F {i : Nat} (hG : topIsG i = false) (leaf step : Nat) (v : Digest) :
    topChainInput leaf i step v = chainInput 0 0 leaf i step v := by
  unfold topChainInput; rw [if_neg (by simp [hG])]
theorem topIsG_iff {i : Nat} (hi : i < 51) : topIsG i = true ↔ i % 2 = 0 := by
  simp [topIsG]; omega

/-- Witness stack: one keygen chain rung (top tree, tree 0) from the end of the header (pc 135, `t3 = CHAIN`, header
words stored) to the loop head 118: the step block, its HASH, `jal 141` and `addi s4,s4,1; jal 118`. It computes
`T3.projHash (topChainHigh i m) (topChainInput leaf i m v)` and writes only `CHAIN+32 .. CHAIN+112`. -/
theorem kpair_rung (sk : BitVec 256) (t : MachineState) (hpc : t.pc = pcOf 135) (leaf i m : Nat) (v : Digest)
    (hi : i < 51) (hm : m < 8) (hmd : m < maxDigit 0 i)
    (h5 : t.getReg .x5 = 0) (h8 : t.getReg .x8 = BitVec.ofNat 64 0)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 i) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 (maxDigit 0 i))
    (h28 : t.getReg .x28 = BitVec.ofNat 64 CHAIN)
    (hz0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0) (hz8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0)
    (h16 : t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (chainHeader 0 0 leaf i m).extractLsb' 0 64)
    (h24 : t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (chainHeader 0 0 leaf i m).extractLsb' 64 64)
    (hv : DigAt t (CHAIN + 48) v) :
    TSim Images.keygenImage sk t (3 + kgX i m) (10 + kgX i m) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' w => w.pc = pcOf (117 + 1) ∧ w.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        DigAt w (CHAIN + 48) v' ∧ RegsExcept t w [.x6, .x7, .x10, .x11, .x12, .x20] ∧
        Frame t w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112)) := by
  obtain ⟨u, su, upc, ur, uf⟩ := ksel_spec t hpc i (by omega) h8 h19
  have hproj : ∀ (high : Bool) (input : T3.HashInput),
      T3.projHash high input = T3.publicHash input >>= fun a => pure (T3.projHalf high a) := by
    intro high input; unfold T3.projHash; rfl
  rw [hproj]
  by_cases hG : topIsG i = true
  · -- G path
    have he : i % 2 = 0 := (topIsG_iff hi).mp hG
    rw [if_pos he] at upc
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t.getReg r := fun r hr => ur.get hr
    obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := ksel2_spec u upc i (by omega) (by rw [g1 _ (by simp)]; exact h19)
    rw [if_neg (by simp [T3.topIsG] at hG; omega)] at u1pc
    have g2 : ∀ r, r ∉ [Reg.x6, .x7] → u1.getReg r = t.getReg r := fun r hr =>
      (u1r.get (by simp at hr ⊢; tauto)).trans (g1 r hr)
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
      kg_spec u1 u1pc i m (by omega) (by omega) hmd (by rw [g2 _ (by simp)]; exact h19)
        (by rw [g2 _ (by simp)]; exact h20) (by rw [g2 _ (by simp)]; exact h21) (by rw [g2 _ (by simp)]; exact h28)
    have f01 : Frame t u1 (fun _ => False) := (uf.trans u1f).mono (fun A _ h => by simp_all)
    have f02 : Frame t u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
      (f01.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12] := ((ur.trans u1r).trans u2r).mono (by simp)
    have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (topChainInput leaf i m v)) := by
      have hl := topChainInput_length leaf i m v
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [wordsOf_topChainInput_G hG, readWords_eight]
      rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
        show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
        show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
        show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
      rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, f01.get (A := CHAIN + 16) (by decide) (by simp),
        f01.get (A := CHAIN + 24) (by decide) (by simp), h16, h24]
    have hvalid : hashArgumentsValid u2 = true := by
      by_cases ht : kterm i m = true
      · rw [if_pos ht] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · rw [if_neg ht] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
    have hf2 : fetch Images.keygenImage u2 = some (.base .ECALL) := (codeAt_kGcall.fetch u2 u2pc).trans rfl
    refine (TSim.steps (su.trans (su1.trans su2)) (TSim.publicHash_bind (k := 3) (c := 3) (n := 0) (b := 0)
      hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
    · obtain ⟨w1, sw1, w1pc, w1r, w1f⟩ := ktail_spec (writeHash u2 a)
        (Or.inl (by rw [pc_writeHash, u2pc, pcOf_add4]))
      have hw20 : w1.getReg .x20 = BitVec.ofNat 64 m := by
        rw [w1r.get (by simp), getReg_writeHash, r02.get (by simp)]; exact h20
      obtain ⟨w, sw, wpc, w20, wr, wf⟩ := kt24_spec w1 w1pc m hw20
      have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
          Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
        (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
          (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
      have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
        by_cases ht : kterm i m = true
        · rw [if_pos ht] at u212; exact hB _ u212 (Or.inr rfl)
        · rw [if_neg ht] at u212; exact hB _ u212 (Or.inl rfl)
      have hval : DigAt (writeHash u2 a) (CHAIN + 48) (T3.projHalf (topChainHigh i m) a) := by
        by_cases ht : kterm i m = true
        · have hh : topChainHigh i m = false := by
            unfold kterm at ht; simp at ht; simp [T3.topChainHigh, ht.1, ht.2]
          rw [if_pos ht] at u212
          rw [hh]
          exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
        · have hh : topChainHigh i m = true := by
            unfold kterm at ht; simp at ht
            by_cases h0 : i = 0
            · subst h0; simp [T3.topChainHigh, T3.topIsG]
            · have hlt : m + 1 < maxDigit 0 i := by have := ht; omega
              simp [T3.topChainHigh, hG, hlt]
          rw [if_neg ht] at u212
          rw [hh]
          exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
      refine TSim.pure_steps (sw1.trans sw) ⟨wpc, w20, hval.frame (w1f.trans wf) (by decide) (by simp) (by simp),
        ?_, ?_⟩
      · have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
        exact (((r02.trans rr).trans w1r).trans wr).mono (by simp)
      · exact (((f02.trans hwf).trans w1f).trans wf).mono (fun A _ h => by
          simp only [CHAIN] at h ⊢; rcases h with ((h | h) | h) | h <;> first | omega | exact h.elim)
    all_goals simp only [kgX, if_pos hG, topChainInput_blocks]
    all_goals omega
  · -- F path (odd chain)
    have hGf : topIsG i = false := by simpa using hG
    have ho : i % 2 = 1 := by have := (topIsG_iff hi).not.mp hG; omega
    rw [if_neg (by omega)] at upc
    rw [topChainInput_F hGf]
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t.getReg r := fun r hr => ur.get hr
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
      kf_spec u upc (by rw [g1 _ (by simp)]; exact h28)
    have f02 : Frame t u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
      (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12] := (ur.trans u2r).mono (by simp)
    have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (chainInput 0 0 leaf i m v)) := by
      have hl : (chainInput 0 0 leaf i m v).length = 64 := by simp [chainInput, bytesLE_length, zero16]
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 CHAIN hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [Packed.wordsOf_chainInput, readWords_eight,
        f02 CHAIN (by decide) (by simp only [CHAIN]; omega), f02 (CHAIN + 8) (by decide) (by simp only [CHAIN]; omega),
        f02 (CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
        f02 (CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), hz0, hz8, h16, h24, u232, u240, v2.1, v2.2]
    have hvalid : hashArgumentsValid u2 = true :=
      hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
        (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
    have hf2 : fetch Images.keygenImage u2 = some (.base .ECALL) := (codeAt_kFcall.fetch u2 u2pc).trans rfl
    refine (TSim.steps (su.trans su2) (TSim.publicHash_bind (k := 3) (c := 3) (n := 0) (b := 0)
      hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
    · obtain ⟨w1, sw1, w1pc, w1r, w1f⟩ := ktail_spec (writeHash u2 a)
        (Or.inr (by rw [pc_writeHash, u2pc, pcOf_add4]))
      have hw20 : w1.getReg .x20 = BitVec.ofNat 64 m := by
        rw [w1r.get (by simp), getReg_writeHash, r02.get (by simp)]; exact h20
      obtain ⟨w, sw, wpc, w20, wr, wf⟩ := kt24_spec w1 w1pc m hw20
      have hwf := Frame.writeHash u2 a (CHAIN + 48) u212 (by decide)
      have hh : topChainHigh i m = false := WCT9_topChainHigh_F hGf
      refine TSim.pure_steps (sw1.trans sw) ⟨wpc, w20, ?_, ?_, ?_⟩
      · rw [hh]; exact (DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)).frame (w1f.trans wf) (by decide)
          (by simp) (by simp)
      · have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
        exact (((r02.trans rr).trans w1r).trans wr).mono (by simp)
      · exact (((f02.trans hwf).trans w1f).trans wf).mono (fun A _ h => by
          simp only [CHAIN] at h ⊢; rcases h with ((h | h) | h) | h <;> first | omega | exact h.elim)
    all_goals simp only [kgX, if_neg hG, Packed.query_blocks]
    all_goals omega
where
  WCT9_topChainHigh_F {i m : Nat} (h : topIsG i = false) : topChainHigh i m = false := by
    simp [T3.topChainHigh, h]

end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Chain ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chainInput chain shortHash header pad64 zero16 maxDigit topChain topIsG
  topChainHigh topChainInput)
open SphincsSecurity (bytesLE bytesLE_length)
macro "sc_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK] at *); omega))
theorem sub0_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_0 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_0 h) s hpc (by simp [st_0, blk117_0.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_0, Result.toState_pc, E.eval]
  · simp [st_0, blk117_0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_0, blk117_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_0, blk117_0.res, rv_simp]
theorem sub1_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1)) (m cap : Nat) (hm : m < 2 ^ 64) (hcap : cap < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h17 : s.getReg .x17 = BitVec.ofNat 64 cap) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = cap then pcOf (b + 2) else pcOf (b + 8)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_1 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_1 h) s hpc (by simp [st_1, blk117_1.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_1, rebase, blk117_1.res, E.eval, CmpOp.eval, h20, h17]
    by_cases hmc : m = cap
    · subst hmc; simp
    · rw [if_neg hmc]
      have : BitVec.ofNat 64 m ≠ BitVec.ofNat 64 cap := fun he => hmc ((ofNat_inj hm hcap).mp he)
      simp [this]
  · intro r hr; cases r <;> simp_all [st_1, blk117_1.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_1, blk117_1.res, rv_simp]
theorem sub2_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
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
  refine ⟨_, symRun_sound hrun (codeAt_sub_2 h) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
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
theorem sub8_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 8)) (m e : Nat) (hm : m < 2 ^ 64) (he : e < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if m = e then pcOf (b + 26) else pcOf (b + 9)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_8 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_8 h) s hpc (by simp [st_8, blk117_8.res, rv_simp]),
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
theorem sub24_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 24)) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (b + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have hrun := run_24 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_24 h) s hpc (by simp [st_24, blk117_24.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_24, Result.toState_pc, E.eval]
  · t3n [st_24, blk117_24.res, h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_24, blk117_24.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_24, blk117_24.res, rv_simp]
theorem sub26_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 26)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_26 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_26 h) s hpc (by simp [st_26, blk117_26.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_26, blk117_26.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_26, blk117_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_26, blk117_26.res, rv_simp]
theorem fetch_sub23 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 23)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_23 h).fetch s hpc).trans rfl
theorem chainInput_length (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, zero16]
theorem wordsOf_chainInput (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (chainInput lay tree leaf i step v) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] :=
  Packed.wordsOf_chainInput lay tree leaf i step v
theorem toQ_chainInput_blocks (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length]), blocks_toQ ⟨by rw [chainInput_length]; omega,
    by rw [chainInput_length]⟩, chainInput_length]
/-- Witness stack: the keygen chain routine runs top chains only (`lay = 0`, tree 0, `e = maxDigit 0 i`); the pad
words `CHAIN+32/40` are no longer assumed zero (the F path clears them, a G step overwrites them). -/
structure ChainPre (s : MachineState) (lay : Layer) (tree leaf i cap e valp ret : Nat) : Prop where
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
  he : e = maxDigit 0 i
  hv8 : valp % 8 = 0
  hv : valp + 16 ≤ 2 ^ 24
  hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 112 ≤ valp
  l0 : lay = 0
  t0 : tree = 0
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def chainRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x29, .x30]
/-- Witness stack: the chain scratch is `CHAIN+16/24` (header) and `CHAIN+32 .. CHAIN+112` (G input / F pads). -/
def ChainW (valp A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨
    (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (valp ≤ A ∧ A < valp + 16)
structure ChainHead (b : Nat) (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) :
    Prop where
  pc : t.pc = pcOf (b + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (ChainW valp)
  val : DigAt t (CHAIN + 48) v
/-- C4 (b3cc11b's `TSim.projHash_bind`, kept local to the keygen): a projected hash (`projHash high`) followed by `f`;
the continuation sees the chosen half. -/
theorem tsim_projHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState} {input : List UInt8}
    {high : Bool} {k c n b : Nat} {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TSim image sk (writeHash s a) k c n b (f (T3.projHalf high a)) Q) :
    TSim image sk s (1 + k) (8 * (toQ (pad64 input)).blocks + c) (1 + n) ((toQ (pad64 input)).blocks + b)
      (T3.projHash high input >>= f) Q := by
  have e : T3.projHash high input >>= f = T3.publicHash input >>= fun a => f (T3.projHalf high a) := by
    unfold T3.projHash; rw [bind_assoc]; simp only [pure_bind]
  rw [e]
  exact TSim.publicHash_bind hf ht0 hv hq h
theorem ksumTo_split (F : Nat → Nat) (a : Nat) : ∀ n, sumTo F (a + 1 + n) = sumTo F a + F a + sumTo (fun j => F (a + 1 + j)) n
  | 0 => by simp [sumTo]
  | n + 1 => by
    rw [show a + 1 + (n + 1) = (a + 1 + n) + 1 by omega, sumTo, ksumTo_split F a n, sumTo]; omega
/-- Witness stack: steps of one keygen chain rung (loop head 118 back to 118): `sub1; sub8`, the header (25) and the
step block (`3 + kgX`). -/
def kRungK (i m : Nat) : Nat := 30 + kgX i m
def kRungC (i m : Nat) : Nat := 37 + kgX i m
/-- Steps of one keygen chain run of `e` hashes (entry 1, per step `kRungK`, exit and value copy 9). -/
def kChainK (i e : Nat) : Nat := sumTo (fun m => kRungK i m) e + 10
def kChainCy (i e : Nat) : Nat := sumTo (fun m => kRungC i m) e + 10
section loop
variable {image : Image} {b : Nat} (hsub : SubAt image b) (sk : BitVec 256) {s0 : MachineState}
  {lay : Layer} {tree leaf i cap e valp ret : Nat} (hpre : ChainPre s0 lay tree leaf i cap e valp ret)
include hsub hpre
omit hpre in
theorem chain_entry (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    ∃ t, Steps image s0 1 1 t ∧ ChainHead b s0 valp 0 seed t := by
  obtain ⟨t, st, tpc, t20, tr, tf⟩ := sub0_spec hsub s0 (by simpa using hpc)
  exact ⟨t, st, ⟨tpc, t20, tr.mono (by simp [chainRegs]), tf.mono (fun _ _ h => h.elim),
    hseed.frame tf (by decide) (by simp) (by simp)⟩⟩
/-- Witness stack: the header from `b + 9` and the step block (`kpair_rung`), from a state `t2` that agrees with the
chain head `t` outside the header words and `valp`. -/
theorem kchain_rung {m : Nat} (hm : m < e) {v : Digest} {t t2 : MachineState}
    (ht : ChainHead b s0 valp m v t) (ht2 : t2.pc = pcOf (b + 9))
    (hr2 : RegsExcept t t2 [.x6, .x7, .x29]) (hf2 : Frame t t2 (fun A => valp ≤ A ∧ A < valp + 16)) :
    TSim image sk t2 (25 + (3 + kgX i m)) (25 + (10 + kgX i m)) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t2 u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have he := hpre.he
  have hi := hpre.hi
  have hvc := hpre.hvc
  have hl0 := hpre.l0
  have ht0 := hpre.t0
  subst hl0 ht0
  obtain ⟨rfl, rfl⟩ := hsub.2.2.2.2
  have g : ∀ r, r ∉ chainRegs → r ∉ [.x6, .x7, .x29] → t2.getReg r = s0.getReg r := fun r hr hr' =>
    (hr2.get hr').trans (ht.regs.get hr)
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  obtain ⟨t3, st3, t3pc, t3x28, t3w, t3w24, t3r, t3f⟩ :=
    sub9_spec hsub t2 ht2 0 0 leaf i m hpre.hroute hpre.hleaf (by omega) (by omega)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x8)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x9)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x18)
    (by rw [g _ (by simp [chainRegs]) (by simp)]; exact hpre.x19)
    (by rw [hr2.get (by simp)]; exact ht.x20)
  have g3 : ∀ r, r ∉ chainRegs → t3.getReg r = s0.getReg r := fun r hr =>
    (t3r.get (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h | h <;> simp [h]))).trans
      (g r hr (fun h => hr (by simp [chainRegs] at h ⊢; rcases h with h | h | h <;> simp [h])))
  have f03 : Frame s0 t3 (fun A => ChainW valp A) := ((ht.frame.trans hf2).trans t3f).mono (fun A _ h => by
    unfold ChainW at *; rcases h with (h | h) | h
    · exact h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h)
  have hv3 : DigAt t3 (CHAIN + 48) v := (ht.val.frame hf2 (by decide) (by omega) (by omega)).frame t3f
    (by decide) (by simp) (by simp)
  have run := kpair_rung sk t3 (by rw [t3pc]) leaf i m v hi (by omega) (by omega)
    ((g3 _ (by simp [chainRegs])).trans hpre.x5)
    ((g3 _ (by simp [chainRegs])).trans hpre.x8)
    ((g3 _ (by simp [chainRegs])).trans hpre.x19)
    (by rw [t3r.get (by simp), hr2.get (by simp)]; exact ht.x20)
    ((g3 _ (by simp [chainRegs])).trans (hpre.x21.trans (by rw [hpre.he])))
    t3x28
    (by rw [f03.get (by decide) (by unfold ChainW; simp only [CHAIN] at *; omega)]; exact hpre.z0)
    (by rw [f03.get (by decide) (by unfold ChainW; simp only [CHAIN] at *; omega)]; exact hpre.z8)
    t3w t3w24 hv3
  refine (TSim.steps st3 run).mono ?_
  intro v' u hu
  refine ⟨⟨hu.1, hu.2.1, ?_, ?_, hu.2.2.1⟩, ?_⟩
  · exact (((ht.regs.trans hr2).trans t3r).trans hu.2.2.2.1).mono (by simp [chainRegs])
  · exact (f03.trans hu.2.2.2.2).mono (fun A _ h => by
      unfold ChainW at *; rcases h with h | h
      · exact h
      · exact Or.inr (Or.inl h))
  · exact (t3f.trans hu.2.2.2.2).mono (fun A _ h => by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h)
theorem chain_step {m : Nat} (hm : m < e) (hmc : m ≠ cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (kRungK i m) (kRungC i m) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧
        Frame t u (fun A => (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112))) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_neg hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc m e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20) (by rw [t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t2pc
  have run := kchain_rung hsub sk hpre hm ht t2pc ((t1r.trans t2r).mono (by simp))
    ((t1f.trans t2f).mono (fun A _ h => by simp_all))
  refine ((TSim.steps (st1.trans st2) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold kRungK; omega
  · unfold kRungC; omega
  · intro v' u hu
    exact ⟨hu.1, ((t1f.trans t2f).trans hu.2).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)⟩
theorem chain_step_cap {m : Nat} (hm : m < e) (hmc : m = cap) {v : Digest} {t : MachineState}
    (ht : ChainHead b s0 valp m v t) :
    TSim image sk t (kRungK i m + 6) (kRungC i m + 6) 1 1
      (T3.projHash (topChainHigh i m) (topChainInput leaf i m v))
      (fun v' u => ChainHead b s0 valp (m + 1) v' u ∧ DigAt u valp v ∧ Frame t u (ChainW valp)) := by
  have hcap := hpre.hcap
  have he := hpre.he
  have hvc := hpre.hvc
  have hvb := hpre.hv
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  have h17 : t.getReg .x17 = BitVec.ofNat 64 cap := by rw [g _ (by simp [chainRegs]), hpre.x17]
  have h21 : t.getReg .x21 = BitVec.ofNat 64 e := by rw [g _ (by simp [chainRegs]), hpre.x21]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 valp := by rw [g _ (by simp [chainRegs]), hpre.x23]
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc m cap (by omega) (by omega) ht.x20 h17
  rw [if_pos hmc] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp)]; exact h23) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc m e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact h21)
  rw [if_neg (by omega)] at t3pc
  have f13 : Frame t t3 (fun A => valp ≤ A ∧ A < valp + 16) :=
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by
      rcases h with (h | h | h) | h <;> first | exact h.elim | omega)
  have run := kchain_rung hsub sk hpre hm ht t3pc (((t1r.trans t2r).trans t3r).mono (by simp)) f13
  have hvv3 : DigAt t3 valp v := hvv.frame t3f (by omega) (by simp) (by simp)
  refine ((TSim.steps (st1.trans (st2.trans st3)) run).of_eq rfl ?_ ?_ rfl rfl).mono ?_
  · unfold kRungK; omega
  · unfold kRungC; omega
  · intro v' u hu
    refine ⟨hu.1, hvv3.frame hu.2 (by omega) (by simp only [CHAIN] at *; omega)
      (by simp only [CHAIN] at *; omega), ?_⟩
    exact (f13.trans hu.2).mono (fun A _ h => by
      unfold ChainW; rcases h with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h))
theorem chain_exit {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e ≠ cap) :
    ∃ u, Steps image t 3 3 u ∧ u.pc = pcOf ret ∧ RegsExcept t u [] ∧ Frame t u (fun _ => False) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_neg hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2r, t2f⟩ := sub8_spec hsub t1 t1pc e e (by omega) (by omega)
    (by rw [t1r.get (by simp)]; exact ht.x20)
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t2pc
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub26_spec hsub t2 t2pc ret
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  exact ⟨t3, st1.trans (st2.trans st3), t3pc, ((t1r.trans t2r).trans t3r).mono (by simp),
    ((t1f.trans t2f).trans t3f).mono (fun A _ h => by simp_all)⟩
theorem chain_exit_cap {v : Digest} {t : MachineState} (ht : ChainHead b s0 valp e v t) (hec : e = cap) :
    ∃ u, Steps image t 9 9 u ∧ u.pc = pcOf ret ∧ DigAt u valp v ∧ RegsExcept t u [.x6, .x7, .x29] ∧
      Frame t u (fun A => valp ≤ A ∧ A < valp + 16) := by
  have he := hpre.he
  have hcap := hpre.hcap
  have hmd : maxDigit 0 i ≤ 7 := by rw [kmd]; split_ifs <;> omega
  have g : ∀ r, r ∉ chainRegs → t.getReg r = s0.getReg r := fun r hr => ht.regs.get hr
  obtain ⟨t1, st1, t1pc, t1r, t1f⟩ := sub1_spec hsub t ht.pc e cap (by omega) (by omega) ht.x20
    (by rw [g _ (by simp [chainRegs]), hpre.x17])
  rw [if_pos hec] at t1pc
  obtain ⟨t2, st2, t2pc, t2v0, t2v8, t2r, t2f⟩ := sub2_spec hsub t1 t1pc valp
    (by rw [t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x23]) hpre.hv8 hpre.hv
  have hvt1 := ht.val.frame t1f (by decide) (by simp) (by simp)
  obtain ⟨t3, st3, t3pc, t3r, t3f⟩ := sub8_spec hsub t2 t2pc e e (by omega) (by omega)
    (by rw [t2r.get (by simp), t1r.get (by simp)]; exact ht.x20)
    (by rw [t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x21])
  rw [if_pos rfl] at t3pc
  obtain ⟨t4, st4, t4pc, t4r, t4f⟩ := sub26_spec hsub t3 t3pc ret
    (by rw [t3r.get (by simp), t2r.get (by simp), t1r.get (by simp), g _ (by simp [chainRegs]), hpre.x1])
  refine ⟨t4, st1.trans (st2.trans (st3.trans st4)), t4pc, ?_, (((t1r.trans t2r).trans t3r).trans t4r).mono
    (by simp), (((t1f.trans t2f).trans t3f).trans t4f).mono (fun A _ h => by
      rcases h with ((h | h | h) | h) | h <;> first | exact h.elim | omega)⟩
  have hvv : DigAt t2 valp v := ⟨t2v0.trans hvt1.1, t2v8.trans hvt1.2⟩
  exact hvv.frame (t3f.trans t4f) (by have := hpre.hv; omega) (by simp) (by simp)
theorem chainRun_tsim (hpc : s0.pc = pcOf b) (seed : Digest) (hseed : DigAt s0 (CHAIN + 48) seed) :
    TSim image sk s0 (kChainK i e) (kChainCy i e) e e
      (do let v ← topChain leaf i 0 cap seed
          let last ← topChain leaf i cap (e - cap) v
          pure (v, last))
      (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
        RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
  have hcap := hpre.hcap
  have hvc := hpre.hvc
  have hvb := hpre.hv
  obtain ⟨t0, st0, h0⟩ := chain_entry hsub hpc seed hseed
  have p1 : TSim image sk t0 (sumTo (fun j => kRungK i (0 + j)) cap) (sumTo (fun j => kRungC i (0 + j)) cap)
      (sumTo (fun _ => 1) cap) (sumTo (fun _ => 1) cap)
      (topChain leaf i 0 cap seed) (fun v t => ChainHead b s0 valp cap v t) := by
    unfold topChain
    exact TSim.foldlM_range' 0 cap _ seed (fun j v t => ChainHead b s0 valp j v t) _ _ _ _
      (fun j hj v t ht => (chain_step hsub sk hpre (m := 0 + j) (by omega) (by omega)
        (by simpa using ht)).mono (fun v' u hu => by simpa using hu.1)) h0
  rcases Nat.lt_or_ge cap e with hlt | hge
  ·
    have hsplit : topChain leaf i cap (e - cap) = fun v =>
        T3.projHash (topChainHigh i cap) (topChainInput leaf i cap v) >>= fun v1 =>
          (List.range' (cap + 1) (e - cap - 1)).foldlM
            (fun value step => T3.projHash (topChainHigh i step) (topChainInput leaf i step value)) v1 := by
      funext v
      unfold topChain
      rw [show e - cap = e - cap - 1 + 1 by omega, List.range'_succ, List.foldlM_cons]
      rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t (kRungK i cap + 6 + (sumTo (fun j => kRungK i (cap + 1 + j)) (e - cap - 1) + 3))
          (kRungC i cap + 6 + (sumTo (fun j => kRungC i (cap + 1 + j)) (e - cap - 1) + 3))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (1 + (sumTo (fun _ => 1) (e - cap - 1) + 0))
          (do let last ← topChain leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hsplit, bind_assoc]
      refine TSim.bind (chain_step_cap hsub sk hpre hlt rfl ht) (fun v1 u hu => ?_)
      have p2 := TSim.foldlM_range' (image := image) (sk := sk) (cap + 1) (e - cap - 1)
        (fun value step => T3.projHash (topChainHigh i step) (topChainInput leaf i step value)) v1
        (fun j v' w => ChainHead b s0 valp (cap + 1 + j) v' w ∧ DigAt w valp v)
        (fun j => kRungK i (cap + 1 + j)) (fun j => kRungC i (cap + 1 + j))
        (fun _ => 1) (fun _ => 1)
        (fun j hj v' w hw => (chain_step hsub sk hpre (m := cap + 1 + j) (by omega) (by omega)
          hw.1).mono (fun v'' w' hw' => ⟨by simpa [Nat.add_assoc] using hw'.1,
            hw.2.frame hw'.2 (by omega) (by simp; omega) (by simp; omega)⟩))
        ⟨by simpa using hu.1, hu.2.1⟩
      refine TSim.bind p2 (fun last w hw => ?_)
      have hw1 : ChainHead b s0 valp e last w := by
        have := hw.1; rwa [show cap + 1 + (e - cap - 1) = e by omega] at this
      obtain ⟨x, stx, xpc, xr, xf⟩ := chain_exit hsub hpre hw1 (by omega)
      exact TSim.pure_steps stx ⟨xpc, hw.2.frame xf (by omega) (by simp) (by simp),
        hw1.val.frame xf (by decide) (by simp) (by simp), (hw1.regs.trans xr).mono (by simp),
        (hw1.frame.trans xf).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold kChainK
      rw [show e = cap + 1 + (e - cap - 1) by omega, ksumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    · unfold kChainCy
      rw [show e = cap + 1 + (e - cap - 1) by omega, ksumTo_split]
      simp only [Nat.zero_add, show cap + 1 + (e - cap - 1) - cap - 1 = e - cap - 1 by omega]
      omega
    all_goals simp only [sumTo_const]
    all_goals omega
  ·
    have he : cap = e := by omega
    have hz : topChain leaf i cap (e - cap) = fun v => pure v := by
      funext v; rw [show e - cap = 0 by omega]; rfl
    have rest : ∀ v t, ChainHead b s0 valp cap v t →
        TSim image sk t 9 9 0 0
          (do let last ← topChain leaf i cap (e - cap) v; pure (v, last))
          (fun r t => t.pc = pcOf ret ∧ DigAt t valp r.1 ∧ DigAt t (CHAIN + 48) r.2 ∧
            RegsExcept s0 t chainRegs ∧ Frame s0 t (ChainW valp)) := by
      intro v t ht
      rw [hz]
      simp only [pure_bind]
      have ht' : ChainHead b s0 valp e v t := he ▸ ht
      obtain ⟨x, stx, xpc, xv, xr, xf⟩ := chain_exit_cap hsub hpre ht' he.symm
      exact TSim.pure_steps stx ⟨xpc, xv, ht'.val.frame xf (by decide) (by simp; omega)
        (by simp; omega), (ht'.regs.trans xr).mono (by simp [chainRegs]),
        (ht'.frame.trans xf).mono (fun A _ h => by
          unfold ChainW at *; rcases h with h | h; exact h; exact Or.inr (Or.inr h))⟩
    refine (TSim.steps st0 (TSim.bind p1 rest)).of_eq rfl ?_ ?_ ?_ ?_
    · unfold kChainK; subst he; simp only [Nat.zero_add]; omega
    · unfold kChainCy; subst he; simp only [Nat.zero_add]; omega
    all_goals simp only [sumTo_const]
    all_goals subst he; omega
end loop
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_MainBlocks ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev MOUT : Nat := 0x20060
abbrev ZDIG : Nat := 0x20460
abbrev DUMMY : Nat := 0x20A00
abbrev TOP : Nat := 0x50000
abbrev REGION : Nat := 0x80020
macro "kg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP,
    REGION, KCOEF] at *); omega))
theorem blk0_spec (s : MachineState) (hpc : s.pc = pcOf 0) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf 26 ∧
      t.getReg .x2 = BitVec.ofNat 64 TOP ∧ t.getReg .x5 = 0 ∧ t.getReg .x8 = BitVec.ofNat 64 0 ∧
      t.getReg .x9 = BitVec.ofNat 64 0 ∧ t.getReg .x18 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 ZDIG ∧ t.getReg .x26 = BitVec.ofNat 64 51 ∧
      t.getReg .x27 = BitVec.ofNat 64 51 ∧ t.getReg .x31 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 PRIV) = s.getMem (BitVec.ofNat 64 0x80) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 8)) = s.getMem (BitVec.ofNat 64 0x88) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 32)) = s.getMem (BitVec.ofNat 64 0x90) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 40)) = s.getMem (BitVec.ofNat 64 0x98) ∧
      t.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0 ∧
      RegsExcept s t [.x2, .x5, .x6, .x7, .x8, .x9, .x18, .x22, .x26, .x27, .x29, .x30, .x31] ∧
      Frame s t (fun A => A = PRIV ∨ A = PRIV + 8 ∨ A = PRIV + 32 ∨ A = PRIV + 40 ∨ A = PRIV + 48 ∨
        A = PRIV + 56) := by
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc (by simp [blk_0.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blk_0.res, E.eval]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp [blk_0.res, rv_simp]
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · simp only [Result.toState_getMem, blk_0.res, PRIV]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [blk_0.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [PRIV] at hn
    simp only [Result.toState_getMem, blk_0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem blk26_spec (s : MachineState) (hpc : s.pc = pcOf 26) (leaf : Nat) (hl : leaf < 2 ^ 63)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if leaf < 4096 then pcOf 28 else pcOf 36) ∧
      t.getReg .x6 = BitVec.ofNat 64 4096 ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_26 codeAt_26 s hpc (by simp [blk_26.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blk_26.res, E.eval, CmpOp.eval, h18,
      ofNat_slt leaf 4096 hl (by norm_num)]
    by_cases h : leaf < 4096 <;> simp [h]
  · simp [blk_26.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_26.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_26.res, rv_simp]
theorem blk28_spec (s : MachineState) (hpc : s.pc = pcOf 28) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h6 : s.getReg .x6 = BitVec.ofNat 64 4096)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 TOP) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (117 + 27) ∧ t.getReg .x1 = pcOf 34 ∧
      t.getReg .x23 = BitVec.ofNat 64 DUMMY ∧
      t.getReg .x25 = BitVec.ofNat 64 (TOP + 16 * (4096 + leaf)) ∧
      RegsExcept s t [.x1, .x7, .x23, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_28 codeAt_28 s hpc (by simp [blk_28.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [blk_28.res, E.eval]
  · simp [blk_28.res, rv_simp]
  · simp [blk_28.res, rv_simp]
  · simp only [Result.toState_getReg, blk_28.res]
    t3n [h18, h6, h2]
    omega
  · intro r hr; simp at hr; cases r <;> simp_all [blk_28.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_28.res, rv_simp]
theorem blk34_spec (s : MachineState) (hpc : s.pc = pcOf 34) (leaf : Nat)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 26 ∧ t.getReg .x18 = BitVec.ofNat 64 (leaf + 1) ∧
      RegsExcept s t [.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_34 codeAt_34 s hpc (by simp [blk_34.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blk_34.res, E.eval]
  · t3n [blk_34.res, h18]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_34.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_34.res, rv_simp]
theorem blk36_spec (s : MachineState) (hpc : s.pc = pcOf 36) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (117 + 113) ∧ t.getReg .x1 = pcOf 39 ∧
      t.getReg .x15 = BitVec.ofNat 64 12 ∧ t.getReg .x21 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x1, .x15, .x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_36 codeAt_36 s hpc (by simp [blk_36.res, rv_simp]), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · simp [blk_36.res, E.eval]
  · simp [blk_36.res, rv_simp]
  · simp [blk_36.res, rv_simp]
  · simp [blk_36.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_36.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_36.res, rv_simp]
theorem blk39_spec (s : MachineState) (hpc : s.pc = pcOf 39) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 277 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_39 codeAt_39 s hpc (by simp [blk_39.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [blk_39.res, E.eval]
  · intro r hr; cases r <;> rfl
  · intro A hA hn; rfl
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from T3M_Keygen_Init ====
section

namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem extractByte_toNat' (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]
theorem word_ext_bytes {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat'] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega
theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) |||
      (b2.zeroExtend 64 <<< (16 : Word)) ||| (b3.zeroExtend 64 <<< (24 : Word)) |||
      (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)
theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl
theorem bytesToWordLE_sk (sk : SecretKey) (j : Nat) (hj : j < 4) :
    bytesToWordLE (((bytes sk).drop (8 * j)).take 8) = sk.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes
  intro i hi
  rw [extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < 32 by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := sk.isLt
  interval_cases j <;> interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega
def kinit (sk : SecretKey) : MachineState :=
  (({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).setReg .x2 (BitVec.ofNat 64 (2 ^ 24))
theorem kinit_pc (sk : SecretKey) : (kinit sk).pc = pcOf 0 := by
  unfold kinit; rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords]; rfl
theorem bytes_length (sk : SecretKey) : (bytes sk).length = 32 := by simp [bytes]
theorem kinit_getMem (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) :
    (kinit sk).getMem (BitVec.ofNat 64 A) =
      if 0x80 ≤ A ∧ A < 0xA0 ∧ (A - 0x80) % 8 = 0 then bytesToWordLE (((bytes sk).drop (A - 0x80)).take 8)
      else 0 := by
  unfold kinit
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x80 A (by rw [bytes_length]; decide) hA,
    bytes_length]
  rfl
theorem kinit_sk (sk : SecretKey) (j : Nat) (hj : j < 4) :
    (kinit sk).getMem (BitVec.ofNat 64 (0x80 + 8 * j)) = sk.extractLsb' (64 * j) 64 := by
  rw [kinit_getMem sk _ (by omega), if_pos (by omega), show 0x80 + 8 * j - 0x80 = 8 * j by omega,
    bytesToWordLE_sk sk j hj]
theorem kinit_zero (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) (h : A < 0x80 ∨ 0xA0 ≤ A) :
    (kinit sk).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [kinit_getMem sk _ hA, if_neg (by omega)]
structure KStart (sk : SecretKey) (s : MachineState) : Prop where
  pc : s.pc = pcOf 26
  x2 : s.getReg .x2 = BitVec.ofNat 64 TOP
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 0
  x18 : s.getReg .x18 = BitVec.ofNat 64 0
  x22 : s.getReg .x22 = BitVec.ofNat 64 ZDIG
  x26 : s.getReg .x26 = BitVec.ofNat 64 51
  x27 : s.getReg .x27 = BitVec.ofNat 64 51
  x31 : s.getReg .x31 = BitVec.ofNat 64 0
  p0 : s.getMem (BitVec.ofNat 64 PRIV) = sk.extractLsb' 0 64
  p8 : s.getMem (BitVec.ofNat 64 (PRIV + 8)) = sk.extractLsb' 64 64
  p32 : s.getMem (BitVec.ofNat 64 (PRIV + 32)) = sk.extractLsb' 128 64
  p40 : s.getMem (BitVec.ofNat 64 (PRIV + 40)) = sk.extractLsb' 192 64
  p48 : s.getMem (BitVec.ofNat 64 (PRIV + 48)) = 0
  p56 : s.getMem (BitVec.ofNat 64 (PRIV + 56)) = 0
  k0 : s.getMem (BitVec.ofNat 64 0x80) = sk.extractLsb' 0 64
  k8 : s.getMem (BitVec.ofNat 64 0x88) = sk.extractLsb' 64 64
  k16 : s.getMem (BitVec.ofNat 64 0x90) = sk.extractLsb' 128 64
  k24 : s.getMem (BitVec.ofNat 64 0x98) = sk.extractLsb' 192 64
  zero : ∀ A < 2 ^ 64, (A < 0x80 ∨ 0xA0 ≤ A) → (A < PRIV ∨ PRIV + 64 ≤ A) →
    s.getMem (BitVec.ofNat 64 A) = 0
theorem kstart (sk : SecretKey) : ∃ s, Steps image (kinit sk) 26 26 s ∧ KStart sk s := by
  obtain ⟨t, st, tpc, t2, t5, t8, t9, t18, t22, t26, t27, t31, tp0, tp8, tp32, tp40, tp48, tp56, -, tf⟩ :=
    blk0_spec (kinit sk) (kinit_pc sk)
  have k : ∀ j < 4, t.getMem (BitVec.ofNat 64 (0x80 + 8 * j)) = sk.extractLsb' (64 * j) 64 := fun j hj =>
    (tf.get (by omega) (by simp only [PRIV]; omega)).trans (kinit_sk sk j hj)
  refine ⟨t, st, tpc, t2, t5, t8, t9, t18, t22, t26, t27, t31, ?_, ?_, ?_, ?_, tp48, tp56, k 0 (by decide),
    k 1 (by decide), k 2 (by decide), k 3 (by decide), ?_⟩
  · rw [tp0]; exact kinit_sk sk 0 (by decide)
  · rw [tp8]; exact kinit_sk sk 1 (by decide)
  · rw [tp32]; exact kinit_sk sk 2 (by decide)
  · rw [tp40]; exact kinit_sk sk 3 (by decide)
  · intro A hA h1 h2
    rw [tf.get hA (by simp only [PRIV] at *; omega), kinit_zero sk A hA h1]
end SigGolfCandidate.T3M.Keygen
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Sign_Search ====
section

section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
set_option maxRecDepth 100000
def cst (n : Nat) : E := .c (BitVec.ofNat 64 n)
def rfs (l : List (Reg × E)) : RegFile := l.foldl (fun rf p => rf.set p.1 p.2) RegFile.init
def mw (a : Nat) (e : E) : Addr × E := (⟨none, BitVec.ofNat 64 a⟩, e)
def fsi (k : Nat) : Nat := sfIdx.getD k 0
def sci (k : Nat) : Nat := scIdx.getD k 0
def dw (k : Nat) : Nat := WCT9.childBase k / 64
def sh (k : Nat) : Nat := [0,0,21,36,0,21,36,0,21].getD k 0
def hasSh (k : Nat) : Bool := k % 3 != 1
def CBASE : Nat := 0xfef000
def resH153 : PRes := ⟨⟨RegFile.init, [], []⟩, pcOf 11003, false, 1, 1, [], none⟩
def resHead (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst (2 ^ 21)), (.x7, cst CBASE)], [], []⟩, if d then pcOf 11007 else pcOf 11172, false,
    if d then 3 else 4, if d then 3 else 4, [⟨.ltu, .reg .x19, cst (2 ^ 21), d⟩], none⟩
def ctrE : E := .bin .sll (.reg .x19) (cst 0)
def resTrial : PRes :=
  ⟨⟨rfs [(.x6, ctrE), (.x10, cst DIG), (.x11, cst 64), (.x12, cst NBUF), (.x28, cst DIG)],
    [mw (DIG + 24) ctrE, mw (DIG + 16) (cst 0)], []⟩, pcOf 11019, true, 12, 12, [], none⟩
def gateE : E := .bin .sltu (.bin .srl (.ld (cst (NBUF + 24))) (cst 50)) (cst 1353)
def resGate (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, gateE), (.x22, .ld (cst NBUF)), (.x28, cst NBUF)], [], []⟩,
    if d then pcOf 11170 else pcOf 11027, false, 7, 7, [⟨.eq, gateE, .c 0, d⟩], none⟩
def resCost0 : PRes := ⟨⟨rfs [(.x20, cst 0), (.x21, cst COST)], [], []⟩, pcOf (fsi 0), false, 3, 3, [], none⟩
def grpE (k : Nat) : E :=
  if hasSh k then .bin .srl (.ld (cst (NBUF + 8 * dw k))) (cst (sh k)) else .ld (cst (NBUF + 8 * dw k))
def childE (k : Nat) : E := if k = 3 ∨ k = 6 then .bin .srl (grpE k) (cst 21) else .bin .and (grpE k) (cst 127)
def fieldE (k : Nat) : E := .bin .srl (.bin .sll (grpE k) (cst 47)) (cst 54)
def fieldLen (k : Nat) : Nat := if hasSh k then 9 else 8
def resField (k : Nat) (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, cst 563), (.x24, childE k), (.x25, fieldE k), (.x28, cst 131072)], [], []⟩,
    if d then pcOf 11170 else pcOf (sci k), false, fieldLen k, fieldLen k,
    [⟨.geu, fieldE k, cst 563, d⟩], none⟩
def resSc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x21) (.reg .x25))], [], []⟩, pcOf (sci k + 1), false, 1, 1, [], none⟩
def resSc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (sci k + 3), false, 1, 1, [], none⟩
def resCc1 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x6, .bin .add (.reg .x7) (.reg .x24))], [], []⟩, pcOf (sci k + 4), false, 1, 1, [], none⟩
def resCc3 (k : Nat) : PRes :=
  ⟨⟨rfs [(.x20, .bin .add (.reg .x20) (.reg .x6))], [], []⟩, pcOf (fsi (k + 1)), false, 1, 1, [], none⟩
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 11170 else pcOf 11164, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
def idxE : E := .bin .srl (.bin .sll (.reg .x22) (cst 0)) (cst 33)
def resFinal : PRes :=
  ⟨⟨rfs [(.x22, idxE), (.x28, cst IDXV)], [mw IDXV idxE], []⟩, pcOf 11175, false, 6, 6, [], none⟩
def resNext : PRes :=
  ⟨⟨rfs [(.x19, .bin .add (.reg .x19) (cst 1))], [], []⟩, pcOf 11003, false, 2, 2, [], none⟩
def resFail : PRes :=
  ⟨⟨rfs [(.x5, cst 1), (.x10, cst 1)], [], []⟩, pcOf 11174, true, 2, 2, [], none⟩
theorem chk_h153 : optBeq (run hookLook [11003] 153 []) resH153 = true := by decide +kernel
theorem chk_head : (optBeq (run headLook [11007, 11172] 11003 [.br true]) (resHead true) &&
    optBeq (run headLook [11007, 11172] 11003 [.br false]) (resHead false)) = true := by decide +kernel
theorem chk_trial : optBeq (run headLook [] 11007 []) resTrial = true := by decide +kernel
theorem chk_gate : (optBeq (run headLook [11170, 11027] 11020 [.br true]) (resGate true) &&
    optBeq (run headLook [11170, 11027] 11020 [.br false]) (resGate false)) = true := by decide +kernel
theorem chk_cost0 : optBeq (run headLook [fsi 0] 11027 []) resCost0 = true := by decide +kernel
theorem chk_fields : (List.range 9).all (fun k =>
    optBeq (run headLook [11170, sci k] (fsi k) [.br true]) (resField k true) &&
    optBeq (run headLook [11170, sci k] (fsi k) [.br false]) (resField k false) &&
    optBeq (run headLook [sci k + 1] (sci k) []) (resSc1 k) &&
    optBeq (run headLook [sci k + 3] (sci k + 2) []) (resSc3 k) &&
    headLook (sci k + 1) == some 0x00034303) = true := by
  decide +kernel
theorem chk_childs : (List.range 9).all (fun k =>
    optBeq (run headLook [sci k + 4] (sci k + 3) []) (resCc1 k) &&
    optBeq (run headLook [fsi (k + 1)] (sci k + 5) []) (resCc3 k) &&
    headLook (sci k + 4) == some 0xf8034303) = true := by
  decide +kernel
theorem chk_cap : (optBeq (run headLook [11170, 11164] 11162 [.br true]) (resCap true) &&
    optBeq (run headLook [11170, 11164] 11162 [.br false]) (resCap false)) = true := by decide +kernel
theorem chk_final : optBeq (run headLook [11175] 11164 []) resFinal = true := by decide +kernel
theorem chk_next : optBeq (run headLook [11003] 11170 []) resNext = true := by decide +kernel
theorem chk_fail : optBeq (run headLook [] 11172 []) resFail = true := by decide +kernel
theorem fsi_nine : fsi 9 = 11162 := by decide +kernel
theorem sci_lt : ∀ k, k < 9 → sci k + 6 = fsi (k + 1) ∧ fsi k < sci k ∧ sci k + 5 < 11162 := by decide +kernel
theorem run_h153 : run hookLook [11003] 153 [] = some resH153 := optBeq_eq chk_h153
theorem run_head (d : Bool) : run headLook [11007, 11172] 11003 [.br d] = some (resHead d) := by
  have h := chk_head
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_trial : run headLook [] 11007 [] = some resTrial := optBeq_eq chk_trial
theorem run_gate (d : Bool) : run headLook [11170, 11027] 11020 [.br d] = some (resGate d) := by
  have h := chk_gate
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_cost0 : run headLook [fsi 0] 11027 [] = some resCost0 := optBeq_eq chk_cost0
theorem chk_fields_k {k : Nat} (hk : k < 9) :
    (optBeq (run headLook [11170, sci k] (fsi k) [.br true]) (resField k true) &&
    optBeq (run headLook [11170, sci k] (fsi k) [.br false]) (resField k false) &&
    optBeq (run headLook [sci k + 1] (sci k) []) (resSc1 k) &&
    optBeq (run headLook [sci k + 3] (sci k + 2) []) (resSc3 k) &&
    headLook (sci k + 1) == some 0x00034303) = true :=
  List.all_eq_true.mp chk_fields k (List.mem_range.mpr hk)
theorem chk_childs_k {k : Nat} (hk : k < 9) :
    (optBeq (run headLook [sci k + 4] (sci k + 3) []) (resCc1 k) &&
    optBeq (run headLook [fsi (k + 1)] (sci k + 5) []) (resCc3 k) &&
    headLook (sci k + 4) == some 0xf8034303) = true :=
  List.all_eq_true.mp chk_childs k (List.mem_range.mpr hk)
theorem run_cc1 (k : Nat) (hk : k < 9) : run headLook [sci k + 4] (sci k + 3) [] = some (resCc1 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1
theorem run_cc3 (k : Nat) (hk : k < 9) : run headLook [fsi (k + 1)] (sci k + 5) [] = some (resCc3 k) := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu2 (k : Nat) (hk : k < 9) : headLook (sci k + 4) = some 0xf8034303 := by
  have h := chk_childs_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_field (k : Nat) (hk : k < 9) (d : Bool) :
    run headLook [11170, sci k] (fsi k) [.br d] = some (resField k d) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.1.1.1.2
  · exact optBeq_eq h.1.1.1.1
theorem run_sc1 (k : Nat) (hk : k < 9) : run headLook [sci k + 1] (sci k) [] = some (resSc1 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.1.2
theorem run_sc3 (k : Nat) (hk : k < 9) : run headLook [sci k + 3] (sci k + 2) [] = some (resSc3 k) := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true] at h
  exact optBeq_eq h.1.2
theorem look_lbu (k : Nat) (hk : k < 9) : headLook (sci k + 1) = some 0x00034303 := by
  have h := chk_fields_k hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2
theorem run_cap (d : Bool) : run headLook [11170, 11164] 11162 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem run_final : run headLook [11175] 11164 [] = some resFinal := optBeq_eq chk_final
theorem run_next : run headLook [11003] 11170 [] = some resNext := optBeq_eq chk_next
theorem run_fail : run headLook [] 11172 [] = some resFail := optBeq_eq chk_fail
end ClaudeWCT.W9.Machine.Sign.SearchM
end
section
namespace ClaudeWCT.W9.Machine.Sign.SearchM
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.T3 (Digest HashOutput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
def costByte (f : Nat) : Nat :=
  if f < 563 then WCT9.routineCosts.getD f 0
  else if 16256 ≤ f then WCT9.maxChildSave - WCT9.childSave (f - 16256)
  else if 1024 ≤ f ∧ f < 1280 then
    (SigGolfCandidate.T3M.Images.signPrefix_4.getD (f - 1024) 0).toNat else 255
def costChk : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | f, b :: bs => (b.toNat == costByte f) && costChk (f + 1) bs
set_option maxRecDepth 100000 in
theorem costBytes_chk : costChk 0 costBytes = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem costBytes_length : costBytes.length = 16384 := by decide +kernel
theorem costChk_getD : ∀ (l : List (BitVec 8)) (f : Nat), costChk f l = true →
    ∀ i, i < l.length → (l.getD i 0).toNat = costByte (f + i)
  | [], _, _, i, hi => absurd hi (by simp)
  | b :: bs, f, h, i, hi => by
    simp only [costChk, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · simpa using h.1
    · have := costChk_getD bs (f + 1) h.2 i (by simpa using hi)
      simpa [show f + 1 + i = f + (i + 1) by omega] using this
theorem costBytes_getD (f : Nat) (hf : f < 16384) : (costBytes.getD f 0).toNat = costByte f := by
  have := costChk_getD costBytes 0 costBytes_chk f (by rw [costBytes_length]; exact hf)
  rwa [Nat.zero_add] at this
theorem costByte_lt (f : Nat) : costByte f < 256 := by
  unfold costByte
  split_ifs with h h2 h3
  · have hm : f < WCT9.routineCosts.length := by rw [WCT9.routineCosts_length]; exact h
    rw [List.getD_eq_getElem _ _ hm]
    have := (WCT9.routineCosts_bounds _ (List.getElem_mem hm)).2
    omega
  · unfold WCT9.maxChildSave; omega
  · exact BitVec.isLt _
  · decide
def childN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ WCT9.childBase c % 128
theorem childN_lt (a : BitVec 256) (c : Nat) : childN a c < 128 := Nat.mod_lt _ (by decide +kernel)
theorem costByte_child (c : Nat) (hc : c < 128) :
    costByte (16256 + c) = WCT9.maxChildSave - WCT9.childSave c := by
  unfold costByte
  rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
theorem costByte_childN (a : HashOutput) (k : WCT9.Coord) :
    costByte (16256 + childN a k.val) = WCT9.childExtra (WCT9.child a k) := by
  rw [costByte_child _ (childN_lt a k.val)]; rfl
theorem costByte_rank (a : HashOutput) (c : WCT9.Coord) (h : WCT9.field a c < 563) :
    costByte (WCT9.field a c) = WCT9.routineCost (WCT9.rank a c) := by
  unfold costByte WCT9.routineCost WCT9.rank
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [WCT9.routineCosts_length]; exact h)]
  simp only [Nat.mod_eq_of_lt h]
theorem cost_byte {s : MachineState} (hc : CostAt s) {f : Nat} (hf : f < 16384) :
    s.getByte (BitVec.ofNat 64 (COST + f)) = BitVec.ofNat 8 (costByte f) := by
  rw [getByte_eq_word s _ (by unfold COST; omega)]
  rw [show (COST + f) / 8 * 8 = COST + 8 * (f / 8) by unfold COST; omega,
    show (COST + f) % 8 = f % 8 by unfold COST; omega, hc (f / 8) (by omega),
    Keygen.extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide +kernel))]
  apply BitVec.eq_of_toNat_eq
  rw [← costBytes_getD f hf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (BitVec.isLt _)]
  congr 1
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos (Nat.mod_lt _ (by decide +kernel)), show 8 * (f / 8) + f % 8 = f by omega]
theorem rfs_get_other (l : List (Reg × E)) (x : Reg) (h : ∀ p ∈ l, p.1 ≠ x) :
    (rfs l).get x = RegFile.init.get x := by
  unfold rfs
  suffices ∀ rf : RegFile, (l.foldl (fun rf p => rf.set p.1 p.2) rf).get x = rf.get x from this _
  induction l with
  | nil => intro rf; rfl
  | cons p l ih =>
    intro rf
    simp only [List.foldl_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq)), RegFile.get_set_ne _ _ (Ne.symm (h p (by simp)))]
theorem piece {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) {stops : List Nat} {n : Nat}
    {dirs : List Dir} {r : PRes} (h : run look stops n dirs = some r) (s : MachineState) (hpc : s.pc = pcOf n)
    (hobl : r.st.obl = []) (hbr : ∀ b ∈ r.brs, b.holds s) (hspc : r.spc = none) :
    Steps im s r.steps r.cycles (r.toState s) ∧ (r.toState s).pc = r.pc ∧
      (r.ecall = true → fetch im (r.toState s) = some (.base .ECALL)) ∧
      (∀ x, (r.toState s).getReg x = (r.st.regs.get x).eval s) ∧
      (∀ a, (r.toState s).getMem a = memEval s r.st.mem a) := by
  obtain ⟨h1, h2⟩ := run_sound hl h s hpc (by rw [hobl]; intro o ho; cases ho) hbr
  exact ⟨h1, PRes.toState_pc' r s hspc, h2, fun x => PRes.toState_getReg' r s x,
    fun a => PRes.toState_getMem' r s a⟩
theorem regs_rfs {t s : MachineState} {l : List (Reg × E)} (h : ∀ x, t.getReg x = ((rfs l).get x).eval s) :
    RegsExcept s t (l.map Prod.fst) := by
  intro x hx
  rw [h x, rfs_get_other l x (fun p hp he => hx (List.mem_map.mpr ⟨p, hp, he⟩)), RegFile.init_get_eval]
theorem mod64_div_mod (x p q : Nat) (h : p + q ≤ 64) : x % 2 ^ 64 / 2 ^ p % 2 ^ q = x / 2 ^ p % 2 ^ q := by
  have e : (2 : Nat) ^ 64 = 2 ^ p * 2 ^ (64 - p) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
theorem ofNat_and_mask (x : Word) (q : Nat) (hq : q ≤ 64) :
    x &&& BitVec.ofNat 64 (2 ^ q - 1) = BitVec.ofNat 64 (x.toNat % 2 ^ q) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (2 : Nat) ^ q - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide +kernel) hq; omega
  have h2 : x.toNat % 2 ^ q < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide +kernel) hq)
  rw [BitVec.toNat_and, toNat_ofNat_lt h1, Nat.and_two_pow_sub_one_eq_mod, toNat_ofNat_lt h2]
theorem and_eval (x y : Word) : BinOp.eval .and x y = x &&& y := rfl
theorem srl_eval (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .srl x (BitVec.ofNat 64 k) = x >>> k := by
  simp only [BinOp.eval, toNat_ofNat_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
theorem shl0_shr33 (a : BitVec 256) : ((a.extractLsb' 0 64) <<< 0) >>> 33 = BitVec.ofNat 64 (WCT9.digestIndex a) := by
  apply BitVec.eq_of_toNat_eq
  rw [WCT9.digestIndex_val]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat, pow_zero, Nat.mul_one, Nat.shiftRight_zero]
  omega
theorem sh_bound (k : Nat) (hk : k < 9) : sh k + 21 ≤ 64 ∧ 64 * dw k + sh k + 7 = WCT9.fieldBase k ∧ dw k < 4 := by
  interval_cases k <;> decide +kernel
theorem sll_eval (x : Word) (k : Nat) (hk : k < 64) : BinOp.eval .sll x (BitVec.ofNat 64 k) = x <<< k := by
  simp only [BinOp.eval, toNat_ofNat_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk]
theorem gateE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) :
    gateE.eval s = BitVec.ofNat 64 (if a.toNat / 2 ^ 242 % 2 ^ 14 < 1353 then 1 else 0) := by
  have h3 : s.getMem (BitVec.ofNat 64 (NBUF + 24)) = a.extractLsb' 192 64 := ha 3 (by decide +kernel)
  simp only [gateE, cst, E.eval, h3]
  rw [srl_eval _ 50 (by decide +kernel)]
  change (if BitVec.ult (a.extractLsb' 192 64 >>> 50) 1353#64 then (1 : BitVec 64) else 0) = _
  rw [show BitVec.ult (a.extractLsb' 192 64 >>> 50) 1353#64 = decide (a.toNat / 2 ^ 242 % 2 ^ 14 < 1353) by
    simp only [BitVec.ult, SigGolfCandidate.Research.V7Composed198Gate.gate_shift50_toNat,
      show (1353#64 : BitVec 64).toNat = 1353 from rfl]]
  by_cases h : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, Bool.false_eq_true, if_false]; rfl

theorem grpE_toNat (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    ((grpE k).eval s).toNat = a.toNat / 2 ^ (64 * dw k) % 2 ^ 64 / 2 ^ sh k := by
  obtain ⟨h21, -, hd⟩ := sh_bound k hk
  have hm := ha (dw k) hd
  unfold grpE
  split_ifs with h0
  · simp only [cst, E.eval, hm]
    rw [srl_eval _ _ (by omega), BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.extractLsb'_toNat,
      Nat.shiftRight_eq_div_pow]
  · have hs0 : sh k = 0 := by interval_cases k <;> simp_all [hasSh, sh]
    simp only [cst, E.eval, hm, hs0, pow_zero, Nat.div_one, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem sll47_srl54 (g : Word) : ((g <<< 47) >>> 54).toNat = g.toNat / 2 ^ 7 % 2 ^ 10 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 64 = 2 ^ 17 * 2 ^ 47 by norm_num, Nat.mul_mod_mul_right,
    show (2 : Nat) ^ 54 = 2 ^ 47 * 2 ^ 7 by norm_num, ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ (by positivity), show (2 : Nat) ^ 17 = 2 ^ 7 * 2 ^ 10 by norm_num,
    Nat.mod_mul_right_div_self]
theorem sll47_srl54' (g : Word) : (g <<< 47) >>> 54 = BitVec.ofNat 64 (g.toNat / 2 ^ 7 % 2 ^ 10) := by
  apply BitVec.eq_of_toNat_eq
  rw [sll47_srl54, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel))]
theorem fieldE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (fieldE k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10) := by
  obtain ⟨h21, hcb, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  simp only [fieldE, cst, E.eval]
  rw [sll_eval _ 47 (by decide +kernel), srl_eval _ 54 (by decide +kernel), sll47_srl54']
  congr 1
  rw [hg, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    mod64_div_mod _ (sh k + 7) 10 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  all_goals omega
def fieldEOld (k : Nat) : E := .bin .and (.bin .srl (grpE k) (cst 7)) (cst 1023)
theorem fieldEOld_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (fieldEOld k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10) := by
  obtain ⟨h21, hcb, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  simp only [fieldEOld, cst, E.eval]
  rw [srl_eval _ 7 (by decide +kernel), and_eval, show (1023 : Nat) = 2 ^ 10 - 1 from rfl, ofNat_and_mask _ 10 (by decide +kernel)]
  congr 1
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hg, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    mod64_div_mod _ (sh k + 7) 10 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  congr 3
  all_goals omega
theorem childE_eval (s : MachineState) (a : BitVec 256) (ha : OutAt s NBUF a) (k : Nat) (hk : k < 9) :
    (childE k).eval s = BitVec.ofNat 64 (a.toNat / 2 ^ WCT9.childBase k % 128) := by
  obtain ⟨h21, -, -⟩ := sh_bound k hk
  have hg := grpE_toNat s a ha k hk
  have hcb : 64 * dw k + sh k + (if k = 3 ∨ k = 6 then 21 else 0) = WCT9.childBase k := by
    interval_cases k <;> decide +kernel
  unfold childE
  split_ifs with h36
  · simp only [cst, E.eval]
    rw [srl_eval _ 21 (by decide +kernel)]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hg, BitVec.toNat_ofNat]
    have hs : sh k = 36 := by rcases h36 with rfl | rfl <;> rfl
    rw [if_pos h36, hs, show 64 * dw k + 36 + 21 = 64 * dw k + (36 + 21) by omega] at hcb
    have hlt : a.toNat / 2 ^ WCT9.childBase k % 128 < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num)
    rw [Nat.mod_eq_of_lt hlt, hs, Nat.div_div_eq_div_mul, ← Nat.pow_add, ← hcb]
    conv_lhs => rw [show (2 : Nat) ^ 64 = 2 ^ (36 + 21) * 2 ^ 7 by norm_num, Nat.mod_mul_right_div_self]
    rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
    rfl
  · simp only [cst, E.eval]
    rw [and_eval, show (127 : Nat) = 2 ^ 7 - 1 from rfl, ofNat_and_mask _ 7 (by decide +kernel)]
    congr 1
    rw [if_neg h36, Nat.add_zero] at hcb
    rw [hg, mod64_div_mod _ (sh k) 7 (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, hcb]
    rfl
section pieces
variable {im : Image}
theorem h153_spec (hl : LookOK im hookLook) (s : MachineState) (hpc : s.pc = pcOf 153) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 11003 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_h153 s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, fun x _ => by rw [hr x]; exact RegFile.init_get_eval s x, fun A _ _ => by rw [hm]; rfl⟩
theorem head_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11003) (i : Nat)
    (hi : i ≤ 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t k, Steps im s k k t ∧ k ≤ 4 ∧ t.pc = (if i < 2 ^ 21 then pcOf 11007 else pcOf 11172) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) ∧ t.getReg .x7 = BitVec.ofNat 64 CBASE := by
  have hbr : ∀ b ∈ (resHead (decide (i < 2 ^ 21))).brs, b.holds s := by
    intro b hb
    simp only [resHead, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, h19, BitVec.ult, toNat_ofNat_lt (by omega : i < 2 ^ 64),
      toNat_ofNat_lt (by decide +kernel : 2 ^ 21 < 2 ^ 64)]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_head _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl, by rw [hr]; rfl⟩
  · simp only [resHead]; split <;> decide +kernel
  · rw [hp]; simp only [resHead]; by_cases h : i < 2 ^ 21 <;> simp [h]
theorem trial_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11007) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 12 12 t ∧ fetch im t = some (.base .ECALL) ∧ t.pc = pcOf 11019 ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 i ∧
      RegsExcept s t [.x6, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 24 ∨ A = DIG + 16) := by
  obtain ⟨hs, hp, he, hr, hm⟩ := piece hl run_trial s hpc rfl (by intro b hb; cases hb) rfl
  have hctr : ctrE.eval s = BitVec.ofNat 64 i := by
    simp only [ctrE, cst, E.eval, BinOp.eval, h19, toNat_ofNat_lt (by decide +kernel : (0 : Nat) < 2 ^ 64)]
    rw [ofNat_shl i 0, pow_zero, Nat.mul_one]
  refine ⟨_, hs, he rfl, hp, by rw [hr]; rfl, by rw [hr]; rfl, by rw [hr]; rfl, ?_, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_neg (by decide +kernel),
      memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl]; rfl
  · rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl, hctr]
  · intro A hA hn
    simp only [not_or] at hn
    rw [hm]; simp only [resTrial, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel), if_neg hn.1, memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel),
      if_neg hn.2]; rfl
theorem gate_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11020) (a : BitVec 256)
    (ha : OutAt s NBUF a) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = (if a.toNat / 2 ^ 242 % 2 ^ 14 < 1353 then pcOf 11027 else pcOf 11170) ∧
      t.getReg .x22 = a.extractLsb' 0 64 ∧ RegsExcept s t [.x6, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  have hg := gateE_eval s a ha
  have hbr : ∀ b ∈ (resGate (decide ¬ (a.toNat / 2 ^ 242 % 2 ^ 14 < 1353))).brs, b.holds s := by
    intro b hb
    simp only [resGate, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hg]
    by_cases h0 : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
    · simp only [h0, if_true, not_true_eq_false, decide_false]; decide +kernel
    · simp only [h0, if_false, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_gate _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · rw [hp]; simp only [resGate]
    by_cases h0 : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
    · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
    · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
  · rw [hr]
    have h0 := ha 0 (by decide +kernel)
    simp only [Nat.mul_zero, Nat.add_zero] at h0
    show s.getMem (BitVec.ofNat 64 NBUF) = _
    exact h0
theorem cost0_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11027) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (fsi 0) ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x21 = BitVec.ofNat 64 COST ∧ RegsExcept s t [.x20, .x21] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_cost0 s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, hp, by rw [hr]; rfl, by rw [hr]; rfl, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
theorem field_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState)
    (hpc : s.pc = pcOf (fsi k)) (a : BitVec 256) (ha : OutAt s NBUF a) :
    ∃ t c, Steps im s c c t ∧ c ≤ 9 ∧
      t.pc = (if WCT9.field a ⟨k, hk⟩ < 563 then pcOf (sci k) else pcOf 11170) ∧
      t.getReg .x25 = BitVec.ofNat 64 (WCT9.field a ⟨k, hk⟩) ∧
      t.getReg .x24 = BitVec.ofNat 64 (childN a k) ∧
      RegsExcept s t [.x6, .x24, .x25, .x28] ∧ Frame s t (fun _ => False) := by
  have hf := fieldE_eval s a ha k hk
  have hfd : WCT9.field a ⟨k, hk⟩ = a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10 := rfl
  have hlt : a.toNat / 2 ^ WCT9.fieldBase k % 2 ^ 10 < 2 ^ 64 :=
    lt_trans (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
  have hbr : ∀ b ∈ (resField k (decide ¬ (WCT9.field a ⟨k, hk⟩ < 563))).brs, b.holds s := by
    intro b hb
    simp only [resField, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, cst, hf, BitVec.ult, toNat_ofNat_lt hlt,
      toNat_ofNat_lt (by decide +kernel : 563 < 2 ^ 64), hfd]
    rw [decide_not]
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_field k hk _) s hpc rfl hbr rfl
  refine ⟨_, _, hs, ?_, ?_, ?_, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  · simp only [resField, fieldLen]; split <;> omega
  · rw [hp]; simp only [resField]
    by_cases h : WCT9.field a ⟨k, hk⟩ < 563 <;> simp [h]
  · rw [hr]; exact hf
  · rw [hr]; exact childE_eval s a ha k hk
theorem decode_lbu : decodeInstruction 0x00034303 = some (.base (.LBU .x6 .x6 0)) := by rfl
theorem lbu_step (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (sci k + 1)) (f : Nat) (hf : f < 16384) (h6 : u.getReg .x6 = BitVec.ofNat 64 (COST + f))
    (hc : CostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (sci k + 2) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte f) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (sci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : headLook ((u.pc.toNat - 0x1000) / 4) = some 0x00034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (sci k + 1) - 0x1000) / 4 = sci k + 1 by omega]
    exact look_lbu k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 0)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu
  have hcl : classify (.base (.LBU .x6 .x6 0)) = some (.load .bu .x6 .x6 (signExtend12 0)) := rfl
  have e : u.getReg .x6 + signExtend12 0 = BitVec.ofNat 64 (COST + f) := by
    rw [h6]; apply BitVec.eq_of_toNat_eq; simp [signExtend12]
  have hacc : accessValid (u.getReg .x6 + signExtend12 0) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show COST + f < 2 ^ 64 by unfold COST; omega), MEMORY_BYTES]
    unfold COST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide +kernel)]
    simp only [LoadKind.read, e, cost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt f
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem sc_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sci k))
    (f S : Nat) (hf : f < 16384) (hS : S + 256 < 2 ^ 64) (h21 : s.getReg .x21 = BitVec.ofNat 64 COST)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 f) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : CostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (sci k + 3) ∧ t.getReg .x20 = BitVec.ofNat 64 (S + costByte f) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_sc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resSc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (COST + f) := by
    rw [hr1]; show s.getReg .x21 + s.getReg .x25 = _; rw [h21, h25, ofNat_add_ofNat]
  have hcu : CostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step hl k hk u hp1 f hf u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_sc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide +kernel), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide +kernel)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
theorem decode_lbu2 : decodeInstruction 0xf8034303 = some (.base (.LBU .x6 .x6 3968)) := by rfl
theorem lbu_step2 (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (u : MachineState)
    (hpc : u.pc = pcOf (sci k + 4)) (c : Nat) (hc' : c < 128) (h6 : u.getReg .x6 = BitVec.ofNat 64 (CBASE + c))
    (hc : CostAt u) :
    ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf (sci k + 5) ∧ v.getReg .x6 = BitVec.ofNat 64 (costByte (16256 + c)) ∧
      RegsExcept u v [.x6] ∧ Frame u v (fun _ => False) := by
  have hb := (sci_lt k hk).2.2
  have hpc' : (u.pc.toNat < 0x1000 || u.pc.toNat % 4 != 0) = false := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega)]; simp
  have hw : headLook ((u.pc.toNat - 0x1000) / 4) = some 0xf8034303 := by
    rw [hpc, pcOf, toNat_ofNat_lt (by omega), show (0x1000 + 4 * (sci k + 4) - 0x1000) / 4 = sci k + 4 by omega]
    exact look_lbu2 k hk
  have hf' : fetch im u = some (.base (.LBU .x6 .x6 3968)) := (fetch_of_look hl hpc' hw u rfl).trans decode_lbu2
  have hcl : classify (.base (.LBU .x6 .x6 3968)) = some (.load .bu .x6 .x6 (signExtend12 3968)) := rfl
  have hse : signExtend12 3968 = BitVec.ofNat 64 (2 ^ 64 - 128) := by decide +kernel
  have hf : 16256 + c < 16384 := by omega
  have e : u.getReg .x6 + signExtend12 3968 = BitVec.ofNat 64 (COST + (16256 + c)) := by
    rw [h6, hse, ofNat_add_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    unfold CBASE COST; omega
  have hacc : accessValid (u.getReg .x6 + signExtend12 3968) LoadKind.bu.width = true := by
    rw [e]
    simp only [accessValid, rangeValid, LoadKind.width, Bool.and_eq_true, decide_eq_true_eq,
      toNat_ofNat_lt (show COST + (16256 + c) < 2 ^ 64 by unfold COST; omega), MEMORY_BYTES]
    unfold COST; omega
  refine ⟨_, Steps.step hf' (by rw [classify_sound hcl]; simp only [Micro.exec, hacc, if_true]; rfl)
    (Steps.refl _), ?_, ?_, ?_, ?_⟩
  · simp only [MachineState.setPC]; rw [hpc]; exact SigGolfCandidate.T3M.pcOf_add4 _
  · rw [MachineState.getReg_setPC, MachineState.getReg_setReg_eq (by decide +kernel)]
    simp only [LoadKind.read, e, cost_byte hc hf]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have := costByte_lt (16256 + c)
    omega
  · intro r hr
    have hne : Reg.x6 ≠ r := fun h => hr (by simp [h])
    rw [MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ hne]
  · intro A _ _; simp
theorem cc_spec (hl : LookOK im headLook) (k : Nat) (hk : k < 9) (s : MachineState) (hpc : s.pc = pcOf (sci k + 3))
    (c S : Nat) (hc' : c < 128) (hS : S + 256 < 2 ^ 64) (h7 : s.getReg .x7 = BitVec.ofNat 64 CBASE)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 c) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) (hc : CostAt s) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf (fsi (k + 1)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (S + costByte (16256 + c)) ∧
      RegsExcept s t [.x6, .x20] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs1, hp1, -, hr1, hm1⟩ := piece hl (run_cc1 k hk) s hpc rfl (by intro b hb; cases hb) rfl
  set u := (resCc1 k).toState s with hu
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (CBASE + c) := by
    rw [hr1]; show s.getReg .x7 + s.getReg .x24 = _; rw [h7, h24, ofNat_add_ofNat]
  have hcu : CostAt u := fun j hj => by rw [hm1]; exact hc j hj
  obtain ⟨v, hs2, hp2, v6, hr2, hf2⟩ := lbu_step2 hl k hk u hp1 c hc' u6 hcu
  obtain ⟨hs3, hp3, -, hr3, hm3⟩ := piece hl (run_cc3 k hk) v hp2 rfl (by intro b hb; cases hb) rfl
  refine ⟨_, (hs1.trans (hs2.trans hs3)).of_eq rfl rfl, hp3, ?_, ?_, ?_⟩
  · rw [hr3]; show v.getReg .x20 + v.getReg .x6 = _
    rw [hr2.get (by decide +kernel), hr1, v6]
    show s.getReg .x20 + _ = _
    rw [h20, ofNat_add_ofNat]
  · exact ((regs_rfs hr1).trans (hr2.trans (regs_rfs hr3))).mono (by decide +kernel)
  · intro A hA hn
    rw [hm3]
    show v.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)
    rw [hf2.get hA hn, hm1]; rfl
def fieldN (a : BitVec 256) (c : Nat) : Nat := a.toNat / 2 ^ WCT9.fieldBase c % 2 ^ 10
def psum (a : BitVec 256) (k : Nat) : Nat :=
  ((List.range k).map fun c => costByte (fieldN a c) + costByte (16256 + childN a c)).sum
theorem psum_succ (a : BitVec 256) (k : Nat) :
    psum a (k + 1) = psum a k + costByte (fieldN a k) + costByte (16256 + childN a k) := by
  simp [psum, List.range_succ, List.sum_append, Nat.add_assoc]
theorem psum_le (a : BitVec 256) (k : Nat) : psum a k ≤ 512 * k := by
  induction k with
  | zero => simp [psum]
  | succ k ih =>
    rw [psum_succ]; have := costByte_lt (fieldN a k); have := costByte_lt (16256 + childN a k); omega
theorem fieldN_lt (a : BitVec 256) (c : Nat) : fieldN a c < 16384 :=
  lt_of_lt_of_le (Nat.mod_lt _ (by decide +kernel)) (by decide +kernel)
theorem fields_from (hl : LookOK im headLook) (a : BitVec 256) :
    ∀ n k, k + n = 9 → ∀ v : MachineState, v.pc = pcOf (fsi k) → OutAt v NBUF a → CostAt v →
      v.getReg .x21 = BitVec.ofNat 64 COST → v.getReg .x7 = BitVec.ofNat 64 CBASE →
      v.getReg .x20 = BitVec.ofNat 64 (psum a k) →
      ∃ t c, Steps im v c c t ∧ c ≤ 15 * n ∧ RegsExcept v t [.x6, .x20, .x24, .x25, .x28] ∧
        Frame v t (fun _ => False) ∧
        (if ∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563
          then t.pc = pcOf 11162 ∧ t.getReg .x20 = BitVec.ofNat 64 (psum a 9) else t.pc = pcOf 11170) := by
  intro n
  induction n with
  | zero =>
    intro k hk v hv _ _ _ _ h20
    have hk9 : k = 9 := by omega
    subst hk9
    refine ⟨v, 0, Steps.refl v, le_refl _, RegsExcept.refl _ _, Frame.refl _ _, ?_⟩
    rw [if_pos (fun k' hk' hle => by omega)]
    exact ⟨by rw [hv, fsi_nine], h20⟩
  | succ n ih =>
    intro k hk v hv ha hc h21 h7 h20
    have hk9 : k < 9 := by omega
    obtain ⟨t1, c1, s1, hc1, p1, x25, x24, r1, f1⟩ := field_spec hl k hk9 v hv a ha
    by_cases hf : WCT9.field a ⟨k, hk9⟩ < 563
    · rw [if_pos hf] at p1
      have hc1' : CostAt t1 := fun j hj => by rw [f1.get (by unfold COST; omega) (fun h => h)]; exact hc j hj
      obtain ⟨t2, s2, p2, x20', r2, f2⟩ := sc_spec hl k hk9 t1 p1 (WCT9.field a ⟨k, hk9⟩) (psum a k)
        (fieldN_lt a k) (by have := psum_le a k; omega) (by rw [r1.get (by decide +kernel)]; exact h21) x25
        (by rw [r1.get (by decide +kernel)]; exact h20) hc1'
      have hc2' : CostAt t2 := fun j hj => by rw [f2.get (by unfold COST; omega) (fun h => h)]; exact hc1' j hj
      obtain ⟨t2b, s2b, p2b, x20b, r2b, f2b⟩ := cc_spec hl k hk9 t2 p2 (childN a k)
        (psum a k + costByte (WCT9.field a ⟨k, hk9⟩)) (childN_lt a k)
        (by have := psum_le a k; have := costByte_lt (WCT9.field a ⟨k, hk9⟩); omega)
        (by rw [r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7)
        (by rw [r2.get (by decide +kernel)]; exact x24) x20' hc2'
      have ha2 : OutAt t2b NBUF a := fun j hj => by
        rw [f2b.get (by simp only [NBUF]; omega) (fun h => h), f2.get (by simp only [NBUF]; omega) (fun h => h),
          f1.get (by simp only [NBUF]; omega) (fun h => h)]
        exact ha j hj
      have hc2 : CostAt t2b := fun j hj => by rw [f2b.get (by unfold COST; omega) (fun h => h)]; exact hc2' j hj
      obtain ⟨t, c, s3, hc3, r3, f3, p3⟩ := ih (k + 1) (by omega) t2b p2b ha2 hc2
        (by rw [r2b.get (by decide +kernel), r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h21)
        (by rw [r2b.get (by decide +kernel), r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7)
        (by rw [x20b, psum_succ]; rfl)
      refine ⟨t, c1 + 3 + 3 + c, ((s1.trans s2).trans s2b).trans s3, by omega,
        (((r1.trans r2).trans r2b).trans r3).mono (by decide +kernel),
        (((f1.trans f2).trans f2b).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hiff : (∀ k' (hk' : k' < 9), k ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) ↔
          (∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) := by
        constructor
        · intro h k' hk' hle; exact h k' hk' (by omega)
        · intro h k' hk' hle
          by_cases he : k' = k
          · subst he; exact hf
          · exact h k' hk' (by omega)
      by_cases hall : ∀ k' (hk' : k' < 9), k + 1 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563
      · rw [if_pos hall] at p3; rw [if_pos (hiff.2 hall)]; exact p3
      · rw [if_neg hall] at p3; rw [if_neg (fun h => hall (hiff.1 h))]; exact p3
    · rw [if_neg hf] at p1
      refine ⟨t1, c1, s1, by omega, r1.mono (by decide +kernel), f1, ?_⟩
      rw [if_neg (fun h => hf (h k hk9 le_rfl))]; exact p1
theorem psum_nine (a : BitVec 256) (h : ∀ c : WCT9.Coord, WCT9.field a c < 563) :
    psum a 9 = WCT9.jointCost a := by
  unfold psum WCT9.jointCost WCT9.coordCost
  rw [show List.range 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl,
    show List.finRange 9 = [0, 1, 2, 3, 4, 5, 6, 7, 8] from rfl]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [← costByte_rank a 0 (h 0), ← costByte_rank a 1 (h 1), ← costByte_rank a 2 (h 2), ← costByte_rank a 3 (h 3),
    ← costByte_rank a 4 (h 4), ← costByte_rank a 5 (h 5), ← costByte_rank a 6 (h 6), ← costByte_rank a 7 (h 7),
    ← costByte_rank a 8 (h 8), ← costByte_childN a 0, ← costByte_childN a 1, ← costByte_childN a 2,
    ← costByte_childN a 3, ← costByte_childN a 4, ← costByte_childN a 5, ← costByte_childN a 6,
    ← costByte_childN a 7, ← costByte_childN a 8]
  rfl
theorem cap_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11162) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 789 then pcOf 11164 else pcOf 11170) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 790 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 790 < 2 ^ 64 by decide +kernel)]
    by_cases h : S < 790 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 789))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 789
    · simp only [show S < 790 by omega, if_true, h0, not_true_eq_false, decide_false]; decide +kernel
    · simp only [show ¬ S < 790 by omega, if_false, h0, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 789
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
theorem checks_spec (hl : LookOK im headLook) (u : MachineState) (hpc : u.pc = pcOf 11020) (a : BitVec 256)
    (ha : OutAt u NBUF a) (hc : CostAt u) (h7 : u.getReg .x7 = BitVec.ofNat 64 CBASE) :
    ∃ t c, Steps im u c c t ∧ c ≤ 147 ∧ RegsExcept u t [.x6, .x7, .x20, .x21, .x22, .x24, .x25, .x28] ∧
      Frame u t (fun _ => False) ∧
      (if WCT9.producerAdmissible a = true then t.pc = pcOf 11164 ∧ t.getReg .x22 = a.extractLsb' 0 64
        else t.pc = pcOf 11170) := by
  obtain ⟨t1, s1, p1, x22, r1, f1⟩ := gate_spec hl u hpc a ha
  have hadm := WCT9.admissible_iff a
  have hprod := WCT9.producerAdmissible_iff a
  by_cases hg : a.toNat / 2 ^ 242 % 2 ^ 14 < 1353
  · rw [if_pos hg] at p1
    obtain ⟨t2, s2, p2, x20, x21, r2, f2⟩ := cost0_spec hl t1 p1
    have ha2 : OutAt t2 NBUF a := fun j hj => by
      rw [f2.get (by simp only [NBUF]; omega) (fun h => h), f1.get (by simp only [NBUF]; omega) (fun h => h)]
      exact ha j hj
    have hc2 : CostAt t2 := fun j hj => by
      rw [f2.get (by unfold COST; omega) (fun h => h), f1.get (by unfold COST; omega) (fun h => h)]; exact hc j hj
    obtain ⟨t3, c3, s3, hc3, r3, f3, p3⟩ := fields_from hl a 9 0 rfl t2 p2 ha2 hc2 x21
      (by rw [r2.get (by decide +kernel), r1.get (by decide +kernel)]; exact h7) (by rw [x20]; rfl)
    have h22 : ∀ {t : MachineState}, RegsExcept t2 t [.x6, .x20, .x24, .x25, .x28] →
        t.getReg .x22 = a.extractLsb' 0 64 := fun h => by rw [h.get (by decide +kernel), r2.get (by decide +kernel)]; exact x22
    have hall : (∀ k' (hk' : k' < 9), 0 ≤ k' → WCT9.field a ⟨k', hk'⟩ < 563) ↔
        ∀ c : WCT9.Coord, WCT9.field a c < 563 :=
      ⟨fun h c => h c.val c.isLt (Nat.zero_le _), fun h k' hk' _ => h ⟨k', hk'⟩⟩
    by_cases hf : ∀ c : WCT9.Coord, WCT9.field a c < 563
    · rw [if_pos (hall.2 hf)] at p3
      obtain ⟨p3, x20'⟩ := p3
      have hS := psum_le a 9
      obtain ⟨t4, s4, p4, r4, f4⟩ := cap_spec hl t3 p3 (psum a 9) (by omega) x20'
      refine ⟨t4, 7 + 3 + c3 + 2, ((s1.trans s2).trans s3).trans s4, by omega,
        (((r1.trans r2).trans r3).trans r4).mono (by decide +kernel),
        (((f1.trans f2).trans f3).trans f4).mono (fun _ _ h => by simp at h), ?_⟩
      have hjc : psum a 9 = WCT9.jointCost a := psum_nine a hf
      by_cases hA : WCT9.producerAdmissible a = true
      · rw [if_pos hA]
        have hcap := (hprod.1 hA).2
        rw [if_pos (by rw [hjc]; exact hcap)] at p4
        exact ⟨p4, by rw [r4.get (by decide +kernel)]; exact h22 r3⟩
      · rw [if_neg hA]
        have hcap : ¬ psum a 9 ≤ 789 := fun h => hA (hprod.2 ⟨hadm.2 ⟨hg, hf⟩, by rw [← hjc]; exact h⟩)
        rw [if_neg hcap] at p4; exact p4
    · rw [if_neg (fun h => hf (hall.1 h))] at p3
      refine ⟨t3, 7 + 3 + c3, (s1.trans s2).trans s3, by omega, ((r1.trans r2).trans r3).mono (by decide +kernel),
        ((f1.trans f2).trans f3).mono (fun _ _ h => by simp at h), ?_⟩
      have hA : ¬ WCT9.producerAdmissible a = true := fun h => hf ((hadm.1 (hprod.1 h).1).2)
      rw [if_neg hA]; exact p3
  · rw [if_neg hg] at p1
    refine ⟨t1, 7, s1, by omega, r1.mono (by decide +kernel), f1, ?_⟩
    have hA : ¬ WCT9.producerAdmissible a = true := fun h => hg ((hadm.1 (hprod.1 h).1).1)
    rw [if_neg hA]; exact p1
theorem final_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11164) (a : BitVec 256)
    (h22 : s.getReg .x22 = a.extractLsb' 0 64) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 11175 ∧ t.getReg .x22 = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      t.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 (WCT9.digestIndex a) ∧
      RegsExcept s t [.x22, .x28] ∧ Frame s t (fun A => A = IDXV) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_final s hpc rfl (by intro b hb; cases hb) rfl
  have hidx : idxE.eval s = BitVec.ofNat 64 (WCT9.digestIndex a) := by
    simp only [idxE, cst, E.eval, h22]
    rw [srl_eval _ 33 (by decide +kernel), sll_eval _ 0 (by decide +kernel)]
    exact shl0_shr33 a
  refine ⟨_, hs, hp, by rw [hr]; exact hidx, ?_, regs_rfs hr, ?_⟩
  · rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ (by decide +kernel) (by decide +kernel), if_pos rfl, hidx]
  · intro A hA hn
    rw [hm]; simp only [resFinal, mw]
    rw [memEval_cons_ofNat _ _ _ _ _ hA (by decide +kernel), if_neg hn]; rfl
theorem next_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11170) (i : Nat)
    (_hi : i < 2 ^ 21) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 11003 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl run_next s hpc rfl (by intro b hb; cases hb) rfl
  refine ⟨_, hs, hp, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hr]
  show s.getReg .x19 + BitVec.ofNat 64 1 = _
  rw [h19, ofNat_add_ofNat]
theorem fail_spec (hl : LookOK im headLook) (s : MachineState) (hpc : s.pc = pcOf 11172) :
    ∃ t, Steps im s 2 2 t ∧ fetch im t = some (.base .ECALL) ∧ FailedS t := by
  obtain ⟨hs, hp, he, hr, -⟩ := piece hl run_fail s hpc rfl (by intro b hb; cases hb) rfl
  exact ⟨_, hs, he rfl, ⟨hp, by rw [hr]; rfl, by rw [hr]; rfl⟩⟩
end pieces
theorem digestInput_length' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (SigGolfCandidate.T3.digestInput rho m c).length = 64 := by
  simp only [SigGolfCandidate.T3.digestInput, List.length_append, bytesLE_length]
theorem pad64_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c) = SigGolfCandidate.T3.digestInput rho m c := by
  unfold SigGolfCandidate.T3.pad64
  rw [digestInput_length']
  simp
theorem wordsOf_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    wordsOf (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 0,
        BitVec.ofNat 64 c.toNat, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput']
  unfold SigGolfCandidate.T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE32]
  have hc := c.isLt
  have h0 : (SigGolfCandidate.T3.digestHeader c).extractLsb' 0 64 = BitVec.ofNat 64 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.digestHeader_toNat]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  have h1 : (SigGolfCandidate.T3.digestHeader c).extractLsb' 64 64 = BitVec.ofNat 64 c.toNat := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.extractLsb'_toNat, SigGolfCandidate.T3.digestHeader_toNat]
    simp only [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    omega
  rw [h0, h1]
  rfl
theorem blocks_digestInput' (rho : Digest) (m : SigGolfCandidate.T3.Message) (c : BitVec 32) :
    (toQ (SigGolfCandidate.T3.pad64 (SigGolfCandidate.T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput', blocks_toQ (by rw [Aligned, digestInput_length']; omega), digestInput_length']
structure LInv (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 11003
  hi : i ≤ 2 ^ 21
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t searchRegs
  frame : Frame s0 t SearchW
theorem outAt_writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    OutAt (writeHash t a) NBUF a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide +kernel) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
theorem costAt_frame {s t : MachineState} (h : CostAt s) (hf : Frame s t SearchW) : CostAt t := fun j hj => by
  rw [hf.get (by unfold COST; omega) (by unfold SearchW COST DIG NBUF IDXV; omega)]; exact h j hj
section loop
variable {im : Image} {sk : BitVec 256}
theorem loop (hl : LookOK im headLook) {s0 : MachineState} {rho : Digest} {m : Message}
    (hpre : SearchPre rho m s0) :
    ∀ F i t, i + F = 2 ^ 21 → LInv s0 i t →
      TBSim im sk t (F * 200 + 100) (WCT9.digestSearch rho m i F) (SearchPost s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, k1, s1, hk1, p1, -, -, -⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨t2, s2, -, hf⟩ := fail_spec hl t1 p1
    exact (TBSim.pure_steps' (sk := sk) (s1.trans s2) (Q := SearchPost s0) (a := none) hf).mono
      (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 21 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, k1, s1, hk1, p1, r1, f1, x7h⟩ := head_spec hl t hI.pc i hI.hi hI.x19
    rw [if_pos hi] at p1
    obtain ⟨u, s2, hfu, p2, h10, h11, h12, h16, h24, r2, f2⟩ :=
      trial_spec hl t1 p1 i hi (by rw [r1.get (by decide +kernel), hI.x19])
    have ru : RegsExcept s0 u searchRegs :=
      ((hI.regs.trans r1).trans r2).mono (by decide +kernel)
    have fu : Frame s0 u SearchW := ((hI.frame.trans f1).trans f2).mono (fun A _ hA => by
      simp only [or_false] at hA
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; rcases hA with hA | hA <;> simp [hA])
    have mem : ∀ A, A < 2 ^ 64 → ¬ SearchW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ SearchW A := by
      intro A hA; simp only [SearchW, DIG, NBUF, IDXV] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide +kernel)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide +kernel)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide +kernel)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide +kernel)
    have hq : hashInput u = toQ (SigGolfCandidate.T3.pad64
        (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput', digestInput_length']) h10 (by decide +kernel)
        (by decide +kernel) h11 (by decide +kernel) ?_
      rw [SigGolfCandidate.T3M.readWords_eight, wordsOf_digestInput', hc, h16, h24,
        mem DIG (by decide +kernel) (nw _ (by omega)), mem (DIG + 8) (by decide +kernel) (nw _ (by omega)),
        mem (DIG + 32) (by decide +kernel) (nw _ (by omega)), mem (DIG + 40) (by decide +kernel) (nw _ (by omega)),
        mem (DIG + 48) (by decide +kernel) (nw _ (by omega)), mem (DIG + 56) (by decide +kernel) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide +kernel), hpre.x5]
    have prog : WCT9.digestSearch rho m i (F + 1) =
        (SigGolfCandidate.T3.publicHash (SigGolfCandidate.T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if WCT9.producerAdmissible output = true then pure (some (BitVec.ofNat 32 i, output))
          else WCT9.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind' hfu h5 hv hq
      (W := 176 + (F * 200 + 100)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput']; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf 11020 := by rw [pc_writeHash, p2, SigGolfCandidate.T3M.pcOf_add4]
    have hN : OutAt (writeHash u a) NBUF a := outAt_writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide +kernel)
    have fuw : Frame s0 (writeHash u a) SearchW := (fu.trans fw).mono (fun A _ hA => by
      rcases hA with hA | hA
      · exact hA
      · unfold SearchW; right; right; left; exact hA)
    obtain ⟨v, c, sv, hcv, rv, fv, pv⟩ := checks_spec hl (writeHash u a) pw a hN (costAt_frame hpre.cost fuw)
      (by rw [getReg_writeHash, r2.get (by decide +kernel)]; exact x7h)
    have rv' : RegsExcept s0 v searchRegs :=
      ((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans rv).mono
        (by decide +kernel)
    have fv' : Frame s0 v SearchW := (fuw.trans fv).mono (fun A _ hA => by
      simp only [or_false] at hA; exact hA)
    have hNv : OutAt v NBUF a := fun j hj => by
      rw [fv.get (by simp only [NBUF]; omega) (fun h => h)]; exact hN j hj
    have x19v : v.getReg .x19 = BitVec.ofNat 64 i := by
      rw [rv.get (by decide +kernel), getReg_writeHash, r2.get (by decide +kernel), r1.get (by decide +kernel), hI.x19]
    by_cases hadm : WCT9.producerAdmissible a = true
    · rw [if_pos hadm] at pv
      simp only [hadm, ↓reduceIte]
      obtain ⟨w, sw, pw', x22w, idxw, rw', fw'⟩ := final_spec hl v pv.1 a pv.2
      refine (TBSim.pure_steps' (sv.trans sw) ?_).mono (by omega) (fun _ _ h => h)
      refine ⟨pw', by rw [rw'.get (by decide +kernel), rv'.get (by decide +kernel), hpre.x5], hadm, ?_, x22w, idxw,
        by rw [hc]; exact hi, ?_, ?_⟩
      · intro j hj; rw [fw'.get (by simp only [NBUF]; omega) (by simp only [IDXV, NBUF]; omega)]; exact hNv j hj
      · exact (rv'.trans rw').mono (by decide +kernel)
      · exact (fv'.trans fw').mono (fun A _ hA => by
          rcases hA with hA | hA
          · exact hA
          · unfold SearchW; right; right; right; exact hA)
    · rw [if_neg hadm] at pv
      simp only [hadm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨w, sw, pw', x19w, rw', fw'⟩ := next_spec hl v pv i hi x19v
      have hI' : LInv s0 (i + 1) w :=
        ⟨pw', by omega, x19w, (rv'.trans rw').mono (by decide +kernel),
          (fv'.trans fw').mono (fun A _ hA => by simp only [or_false] at hA; exact hA)⟩
      exact (TBSim.steps (sv.trans sw) (ih (i + 1) w (by omega) hI')).mono (by omega) (fun _ _ h => h)
end loop
end ClaudeWCT.W9.Machine.Sign.SearchM
namespace ClaudeWCT.W9.Machine.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign.SearchM
theorem searchGood (im : Image) : SearchGood im := by
  intro hnew hhooks sk rho m s hpre
  obtain ⟨t0, s0, p0, r0, f0⟩ := h153_spec (hookLook_ok hhooks) s hpre.pc
  have hI : LInv s 0 t0 :=
    ⟨p0, by norm_num, by rw [r0.get (by simp), hpre.x19], r0.mono (by intro x hx; simp at hx),
      f0.mono (fun _ _ h => h.elim)⟩
  have := TBSim.steps (sk := sk) s0
    (loop (headLook_ok hnew) hpre (2 ^ 21) 0 t0 (by norm_num) hI)
  refine this.mono ?_ (fun _ _ h => h)
  unfold searchC trialC WCT9.digestAttemptLimit
  omega
end ClaudeWCT.W9.Machine.Sign
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Code ====
section

namespace ClaudeWCT.W9.Machine.Expand
def expChunk_4 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_4
def expChunk_5 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_5
def expChunk_6 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_6
def expChunk_7 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_7
def expChunk_8 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_8
def expChunk_9 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_9
def expChunk_10 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_10
def expChunk_11 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_11
def expChunk_12 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_12
def expChunk_13 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_13
def expChunk_14 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_14
def expChunk_15 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_15
def expChunk_16 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_16
def expChunk_17 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_17
def expChunk_18 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_18
def expChunk_19 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_19
def expChunk_20 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_20
def expChunk_21 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_21
def expChunk_22 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_22
def expChunk_23 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_23
def expChunk_24 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_24
def expChunk_25 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_25
def expChunk_26 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_26
def expChunk_27 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_27
def expChunk_28 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_28
def expChunk_29 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_29
def expChunk_30 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_30
def expChunk_31 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_31
def expChunk_32 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_32
def expChunk_33 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_33
def expChunk_34 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_34
def expChunk_35 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_35
def expChunk_36 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_36
def expChunk_37 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_37
def expChunk_38 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_38
def expChunk_39 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_39
def expChunk_40 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_40
def expChunk_41 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_41
def expChunk_42 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_42
def expChunk_43 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_43
def expChunk_44 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_44
def expChunk_45 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_45
def expChunk_46 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_46
def expChunk_47 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_47
def expChunk_48 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_48
def expChunk_49 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_49
def expChunk_50 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_50
def expChunk_51 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_51
def expChunk_52 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_52
def expChunk_53 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_53
def expChunk_54 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_54
def expChunk_55 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_55
def expChunk_56 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_56
def expChunk_57 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_57
def expChunk_58 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_58
def expChunk_59 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_59
def expChunk_60 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_60
def expChunk_61 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_61
def expChunk_62 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_62
def expChunk_63 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_63
def expChunk_64 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_64
def expChunk_65 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_65
def expChunk_66 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_66
def expChunk_67 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_67
def expChunk_68 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_68
def expChunk_69 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_69
def expChunk_70 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_70
def expChunk_71 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_71
def expChunk_72 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_72
def expChunk_73 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_73
def expChunk_74 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_74
def expChunk_75 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_75
def expChunk_76 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_76
def expChunk_77 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_77
def expChunk_78 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_78
def expChunk_79 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_79
def expChunk_80 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_80
def expChunk_81 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_81
def expChunk_82 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_82
def expChunk_83 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_83
def expChunk_84 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_84
def expChunk_85 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_85
def expChunk_86 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_86
def expChunk_87 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_87
def expChunk_88 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_88
def expChunk_89 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_89
def expChunk_90 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_90
def expChunk_91 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_91
def expChunk_92 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_92
def expChunk_93 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_93
def expChunk_94 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_94
def expChunk_95 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_95
def expChunk_96 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_96
def expChunk_97 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_97
def expChunk_98 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_98
def expChunk_99 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_99
def expChunk_100 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_100
def expChunk_101 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_101
def expChunk_102 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_102
def expChunk_103 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_103
def expChunk_104 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_104
def expChunk_105 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_105
def expChunk_106 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_106
def expChunk_107 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_107
def expChunk_108 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_108
def expChunk_109 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_109
def expChunk_110 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_110
def expChunk_111 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_111
def expChunk_112 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_112
def expChunk_113 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_113
def expChunk_114 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_114
def expChunk_115 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_115
def expChunk_116 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_116
def expChunk_117 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_117
def expChunk_118 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_118
def expChunk_119 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_119
def expChunk_120 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_120
def expChunk_121 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_121
def expChunk_122 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_122
def expChunk_123 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_123
def expChunk_124 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_124
def expChunk_125 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_125
def expChunk_126 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_126
def expChunk_127 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_127
def expChunk_128 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_128
def expChunk_129 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_129
def expChunk_130 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_130
def expChunk_131 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_131
def expChunk_132 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_132
def expChunk_133 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_133
def expChunk_134 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_134
def expChunk_135 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_135
def expChunk_136 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_136
def expChunk_137 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_137
def expChunk_138 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_138
def expChunk_139 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_139
def expChunk_140 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_140
def expChunk_141 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_141
def expChunk_142 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_142
def expChunk_143 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_143
def expChunk_144 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_144
def expChunk_145 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_145
def expChunk_146 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_146
def expChunk_147 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_147
def expChunk_148 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_148
def expChunk_149 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_149
def expChunk_150 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_150
def expChunk_151 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_151
def expChunk_152 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_152
def expChunk_153 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_153
def expChunk_154 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_154
def expChunk_155 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_155
def expChunk_156 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_156
def expChunk_157 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_157
def expChunk_158 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_158
def expChunk_159 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_159
def expChunk_160 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_160
def expChunk_161 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_161
def expChunk_162 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_162
def expChunk_163 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_163
def expChunk_164 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_164
def expChunk_165 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_165
def expChunk_166 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_166
def expChunk_167 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_167
def expChunk_168 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_168
def expChunk_169 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandCode_169  -- pairing stage 1: installed (constructor/top-path edits)
def expChunk_170 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandCode_170  -- pairing stage 1: installed (chain step block 43764)
def expChunk_171 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_171
def expChunk_172 : List (BitVec 32) := SigGolfCandidate.T3M.Images.expandReferenceCode_172
def expChunks : List (List (BitVec 32)) := [expChunk_4, expChunk_5, expChunk_6, expChunk_7, expChunk_8, expChunk_9, expChunk_10, expChunk_11, expChunk_12, expChunk_13, expChunk_14, expChunk_15, expChunk_16, expChunk_17, expChunk_18, expChunk_19, expChunk_20, expChunk_21, expChunk_22, expChunk_23, expChunk_24, expChunk_25, expChunk_26, expChunk_27, expChunk_28, expChunk_29, expChunk_30, expChunk_31, expChunk_32, expChunk_33, expChunk_34, expChunk_35, expChunk_36, expChunk_37, expChunk_38, expChunk_39, expChunk_40, expChunk_41, expChunk_42, expChunk_43, expChunk_44, expChunk_45, expChunk_46, expChunk_47, expChunk_48, expChunk_49, expChunk_50, expChunk_51, expChunk_52, expChunk_53, expChunk_54, expChunk_55, expChunk_56, expChunk_57, expChunk_58, expChunk_59, expChunk_60, expChunk_61, expChunk_62, expChunk_63, expChunk_64, expChunk_65, expChunk_66, expChunk_67, expChunk_68, expChunk_69, expChunk_70, expChunk_71, expChunk_72, expChunk_73, expChunk_74, expChunk_75, expChunk_76, expChunk_77, expChunk_78, expChunk_79, expChunk_80, expChunk_81, expChunk_82, expChunk_83, expChunk_84, expChunk_85, expChunk_86, expChunk_87, expChunk_88, expChunk_89, expChunk_90, expChunk_91, expChunk_92, expChunk_93, expChunk_94, expChunk_95, expChunk_96, expChunk_97, expChunk_98, expChunk_99, expChunk_100, expChunk_101, expChunk_102, expChunk_103, expChunk_104, expChunk_105, expChunk_106, expChunk_107, expChunk_108, expChunk_109, expChunk_110, expChunk_111, expChunk_112, expChunk_113, expChunk_114, expChunk_115, expChunk_116, expChunk_117, expChunk_118, expChunk_119, expChunk_120, expChunk_121, expChunk_122, expChunk_123, expChunk_124, expChunk_125, expChunk_126, expChunk_127, expChunk_128, expChunk_129, expChunk_130, expChunk_131, expChunk_132, expChunk_133, expChunk_134, expChunk_135, expChunk_136, expChunk_137, expChunk_138, expChunk_139, expChunk_140, expChunk_141, expChunk_142, expChunk_143, expChunk_144, expChunk_145, expChunk_146, expChunk_147, expChunk_148, expChunk_149, expChunk_150, expChunk_151, expChunk_152, expChunk_153, expChunk_154, expChunk_155, expChunk_156, expChunk_157, expChunk_158, expChunk_159, expChunk_160, expChunk_161, expChunk_162, expChunk_163, expChunk_164, expChunk_165, expChunk_166, expChunk_167, expChunk_168, expChunk_169, expChunk_170, expChunk_171, expChunk_172]
def lplanBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_0, SigGolfCandidate.T3M.Images.expandPrefix_1, SigGolfCandidate.T3M.Images.expandPrefix_2, SigGolfCandidate.T3M.Images.expandPrefix_3, SigGolfCandidate.T3M.Images.expandPrefix_4, SigGolfCandidate.T3M.Images.expandPrefix_5].flatten
def planBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_6, SigGolfCandidate.T3M.Images.expandPrefix_7, SigGolfCandidate.T3M.Images.expandPrefix_8, SigGolfCandidate.T3M.Images.expandPrefix_9].flatten
def expCostBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_10, SigGolfCandidate.T3M.Images.expandPrefix_11, SigGolfCandidate.T3M.Images.expandPrefix_12, SigGolfCandidate.T3M.Images.expandPrefix_13, SigGolfCandidate.T3M.Images.expandPrefix_14, SigGolfCandidate.T3M.Images.expandPrefix_15, SigGolfCandidate.T3M.Images.expandPrefix_16, SigGolfCandidate.T3M.Images.expandPrefix_17, SigGolfCandidate.T3M.Images.expandPrefix_18, SigGolfCandidate.T3M.Images.expandPrefix_19, SigGolfCandidate.T3M.Images.expandPrefix_20, SigGolfCandidate.T3M.Images.expandPrefix_21, SigGolfCandidate.T3M.Images.expandPrefix_22, SigGolfCandidate.T3M.Images.expandPrefix_23, SigGolfCandidate.T3M.Images.expandPrefix_24, SigGolfCandidate.T3M.Images.expandPrefix_25, SigGolfCandidate.T3M.Images.expandPrefix_26, SigGolfCandidate.T3M.Images.expandPrefix_27, SigGolfCandidate.T3M.Images.expandPrefix_28, SigGolfCandidate.T3M.Images.expandPrefix_29, SigGolfCandidate.T3M.Images.expandPrefix_30, SigGolfCandidate.T3M.Images.expandPrefix_31, SigGolfCandidate.T3M.Images.expandPrefix_32, SigGolfCandidate.T3M.Images.expandPrefix_33, SigGolfCandidate.T3M.Images.expandPrefix_34, SigGolfCandidate.T3M.Images.expandPrefix_35, SigGolfCandidate.T3M.Images.expandPrefix_36, SigGolfCandidate.T3M.Images.expandPrefix_37, SigGolfCandidate.T3M.Images.expandPrefix_38, SigGolfCandidate.T3M.Images.expandPrefix_39, SigGolfCandidate.T3M.Images.expandPrefix_40, SigGolfCandidate.T3M.Images.expandPrefix_41, SigGolfCandidate.T3M.Images.expandPrefix_42, SigGolfCandidate.T3M.Images.expandPrefix_43, SigGolfCandidate.T3M.Images.expandPrefix_44, SigGolfCandidate.T3M.Images.expandPrefix_45, SigGolfCandidate.T3M.Images.expandPrefix_46, SigGolfCandidate.T3M.Images.expandPrefix_47, SigGolfCandidate.T3M.Images.expandPrefix_48, SigGolfCandidate.T3M.Images.expandPrefix_49, SigGolfCandidate.T3M.Images.expandPrefix_50, SigGolfCandidate.T3M.Images.expandPrefix_51, SigGolfCandidate.T3M.Images.expandPrefix_52, SigGolfCandidate.T3M.Images.expandPrefix_53, SigGolfCandidate.T3M.Images.expandPrefix_54, SigGolfCandidate.T3M.Images.expandPrefix_55, SigGolfCandidate.T3M.Images.expandPrefix_56, SigGolfCandidate.T3M.Images.expandPrefix_57, SigGolfCandidate.T3M.Images.expandPrefix_58, SigGolfCandidate.T3M.Images.expandPrefix_59, SigGolfCandidate.T3M.Images.expandPrefix_60, SigGolfCandidate.T3M.Images.expandPrefix_61, SigGolfCandidate.T3M.Images.expandPrefix_62, SigGolfCandidate.T3M.Images.expandPrefix_63, SigGolfCandidate.T3M.Images.expandPrefix_64, SigGolfCandidate.T3M.Images.expandPrefix_65, SigGolfCandidate.T3M.Images.expandPrefix_66, SigGolfCandidate.T3M.Images.expandPrefix_67, SigGolfCandidate.T3M.Images.expandPrefix_68, SigGolfCandidate.T3M.Images.expandPrefix_69, SigGolfCandidate.T3M.Images.expandPrefix_70, SigGolfCandidate.T3M.Images.expandPrefix_71, SigGolfCandidate.T3M.Images.expandPrefix_72, SigGolfCandidate.T3M.Images.expandPrefix_73].flatten
def hdrBankBytes : List (BitVec 8) := [SigGolfCandidate.T3M.Images.expandPrefix_74, SigGolfCandidate.T3M.Images.expandPrefix_75, SigGolfCandidate.T3M.Images.expandPrefix_76, SigGolfCandidate.T3M.Images.expandPrefix_77, SigGolfCandidate.T3M.Images.expandPrefix_78, SigGolfCandidate.T3M.Images.expandPrefix_79, SigGolfCandidate.T3M.Images.expandPrefix_80, SigGolfCandidate.T3M.Images.expandPrefix_81, SigGolfCandidate.T3M.Images.expandPrefix_82, SigGolfCandidate.T3M.Images.expandPrefix_83, SigGolfCandidate.T3M.Images.expandPrefix_84, SigGolfCandidate.T3M.Images.expandPrefix_85, SigGolfCandidate.T3M.Images.expandPrefix_86, SigGolfCandidate.T3M.Images.expandPrefix_87, SigGolfCandidate.T3M.Images.expandPrefix_88, SigGolfCandidate.T3M.Images.expandPrefix_89, SigGolfCandidate.T3M.Images.expandPrefix_90, SigGolfCandidate.T3M.Images.expandPrefix_91].flatten
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_VLib ====
section

namespace ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (header pad64 zero16 Digest HashOutput HashInput)
open SphincsSecurity (bytesLE bytesLE_length)
set_option linter.unusedSimpArgs false
def cfg0 : Config := {}
def keepB (rs : List Reg) (r : PRes) : Bool := rs.all fun x => E.beq (r.st.regs.get x) (.reg x)
theorem PRes.toState_getReg (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _
theorem PRes.toState_getMem (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl
theorem PRes.toState_pc (r : PRes) (s : MachineState) (h : r.spc = none := by rfl) :
    (r.toState s).pc = r.pc := by
  simp [PRes.toState, PRes.finalPc, h]
theorem keepB_ok {rs : List Reg} {r : PRes} (h : keepB rs r = true) (s : MachineState) :
    ∀ x ∈ rs, (r.toState s).getReg x = s.getReg x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [PRes.toState_getReg, E.beq_eq this]; rfl
theorem br_ne_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, x, .c 0, d⟩ ↔ (decide (x.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]
def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)
theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega
theorem hashArgs_of (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha8 : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd8 : d % 8 = 0)
    (hd : d + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true :=
  hashArgs_ofNat t a n d h10 h11 h12 (by omega) (by omega) (by omega) (by
    unfold hashArgsB
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨decide_eq_true ha8, decide_eq_true hn⟩, decide_eq_true ?_⟩, decide_eq_true ⟨?_, hd8⟩⟩,
      decide_eq_true ?_⟩ <;> unfold MEMORY_BYTES <;> omega)
theorem ofNat_eq_iff' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]
theorem ofNat_ne' {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff' ha hb).mp h')
theorem memEval_cons_ofNat (s : MachineState) (k A : Nat) (v : E) (ws : SymMem) (hA : A < 2 ^ 64)
    (hk : k < 2 ^ 64) :
    memEval s ((⟨none, BitVec.ofNat 64 k⟩, v) :: ws) (BitVec.ofNat 64 A) =
      if A = k then v.eval s else memEval s ws (BitVec.ofNat 64 A) := by
  rw [memEval_cons]
  have e : Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ = BitVec.ofNat 64 k := rfl
  by_cases h : A = k
  · subst h; rw [if_pos e.symm, if_pos rfl]
  · have hne : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, BitVec.ofNat 64 k⟩ := by
      rw [e]; exact ofNat_ne' hA hk h
    rw [if_neg hne, if_neg h]
abbrev dlo (d : BitVec 128) : Word := d.extractLsb' 0 64
abbrev dhi (d : BitVec 128) : Word := d.extractLsb' 64 64
def blk4 (a b c d : BitVec 128) : List UInt8 := bytesLE 16 a ++ bytesLE 16 b ++ bytesLE 16 c ++ bytesLE 16 d
theorem blk4_length (a b c d : BitVec 128) : (blk4 a b c d).length = 64 := by
  simp only [blk4, List.length_append, bytesLE_length]
theorem pad64_blk4 (a b c d : BitVec 128) : pad64 (blk4 a b c d) = blk4 a b c d :=
  pad64_of_aligned _ (by rw [blk4_length])
theorem wordsOf_blk4 (a b c d : BitVec 128) :
    wordsOf (blk4 a b c d) = [dlo a, dhi a, dlo b, dhi b, dlo c, dhi c, dlo d, dhi d] := by
  unfold blk4
  rw [wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length]),
    wordsOf_append _ _ (by simp only [bytesLE_length]),
    wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_bytesLE16]
  rfl
theorem aligned_blk4 (a b c d : BitVec 128) : Aligned (blk4 a b c d) := by
  rw [Aligned, blk4_length]; omega
theorem blocks_blk4 (a b c d : BitVec 128) : (toQ (pad64 (blk4 a b c d))).blocks = 1 := by
  rw [pad64_blk4, blocks_toQ (aligned_blk4 a b c d), blk4_length]
theorem bytesLE16_zero : bytesLE 16 (0 : BitVec 128) = zero16 := by decide
def forestInput (index : Nat) (roots : List Digest) : HashInput :=
  bytesLE 16 (roots.getD 0 0) ++ bytesLE 16 (header 11 0 index 0 0) ++ (roots.drop 1).flatMap (bytesLE 16)
theorem sum_map_16 : ∀ l : List Digest, (l.map fun _ => (16 : Nat)).sum = 16 * l.length
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, List.sum_cons, sum_map_16 l, List.length_cons]; ring
theorem forestInput_length (index : Nat) (roots : List Digest) (h : roots.length = 7) :
    (forestInput index roots).length = 128 := by
  unfold forestInput
  simp only [List.length_append, bytesLE_length, List.length_flatMap]
  rw [sum_map_16, List.length_drop, h]
theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, ofNat_add8, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega
theorem readWords_eight' (t : MachineState) (A : Nat) (hA : A + 64 < 2 ^ 64) :
    t.readWords (BitVec.ofNat 64 A) 8 =
      [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] := by
  rw [readWords_ofNat t A 8 (by omega)]
  rfl
theorem hashInput_words8 (t : MachineState) (l : List UInt8) (A : Nat) (hl : l.length = 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0) (hA' : A + 64 < 2 ^ 64)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw : [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8)),
        t.getMem (BitVec.ofNat 64 (A + 16)), t.getMem (BitVec.ofNat 64 (A + 24)),
        t.getMem (BitVec.ofNat 64 (A + 32)), t.getMem (BitVec.ofNat 64 (A + 40)),
        t.getMem (BitVec.ofNat 64 (A + 48)), t.getMem (BitVec.ofNat 64 (A + 56))] = wordsOf l) :
    hashInput t = toQ l :=
  hashInput_toQ t l 0 A hl h10 hA (by omega) h11 (by norm_num) (by rw [readWords_eight' t A hA']; exact hw)
theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := getReg_writeHash s ans r
theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := pc_writeHash s ans
theorem writeHash_lo (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = dlo (ans.extractLsb' 0 128) ∧
      (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = dhi (ans.extractLsb' 0 128) :=
  DigAt.writeHash_lo t ans d hd hd'
theorem replaceByte_toNat (w : BitVec 64) (pos : Nat) (hp : pos < 8) (b : BitVec 8) :
    (replaceByte w pos b).toNat =
      w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) := by
  have hb := b.isLt
  have hw := w.isLt
  have hlt : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) < 2 ^ 64 := by
    have h1 : w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) + w.toNat % 2 ^ (8 * pos + 8) = w.toNat := Nat.div_add_mod _ _
    have h3 : 2 ^ (8 * pos + 8) = 2 ^ (8 * pos) * 256 := by rw [Nat.pow_add]
    have h4 : w.toNat % 2 ^ (8 * pos) ≤ w.toNat % 2 ^ (8 * pos + 8) := by
      rw [h3, Nat.mod_mul]; omega
    have h5 : 2 ^ (8 * pos) * b.toNat + w.toNat % 2 ^ (8 * pos) < 2 ^ (8 * pos + 8) := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos)) (show b.toNat ≤ 255 by omega)
      rw [h3]; omega
    have h6 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) ≤ w.toNat := by omega
    have h7 : 2 ^ (8 * pos + 8) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    have h8 : w.toNat / 2 ^ (8 * pos + 8) < 2 ^ 64 / 2 ^ (8 * pos + 8) := by
      apply Nat.div_lt_div_of_lt_of_dvd h7 hw
    have h9 : 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8) + 1) ≤ 2 ^ 64 := by
      have := Nat.mul_le_mul_left (2 ^ (8 * pos + 8)) (show w.toNat / 2 ^ (8 * pos + 8) + 1 ≤ 2 ^ 64 / 2 ^ (8 * pos + 8) by omega)
      rwa [Nat.mul_div_cancel' h7] at this
    rw [Nat.mul_add, Nat.mul_one] at h9
    omega
  have key : replaceByte w pos b = BitVec.ofNat 64
      (w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8))) := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    unfold replaceByte
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_ofNat, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and]
    have e : w.toNat % 2 ^ (8 * pos) + 2 ^ (8 * pos) * b.toNat + 2 ^ (8 * pos + 8) * (w.toNat / 2 ^ (8 * pos + 8)) =
        2 ^ (8 * pos) * (2 ^ 8 * (w.toNat / 2 ^ (8 * pos + 8)) + b.toNat) + w.toNat % 2 ^ (8 * pos) := by
      rw [Nat.pow_add]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _)),
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
    simp only [← BitVec.testBit_toNat]
    by_cases h1 : j < 8 * pos
    · simp [h1, show j < pos * 8 by omega]
    · by_cases h2 : j - 8 * pos < 8
      · have : Nat.testBit 255 (j - pos * 8) = true := by
          have : j - pos * 8 < 8 := by omega
          interval_cases (j - pos * 8) <;> decide
        simp [h1, show ¬ j < pos * 8 by omega, show j - pos * 8 < 64 by omega, this,
          show j - 8 * pos = j - pos * 8 by omega]
        intro h; omega
      · have : Nat.testBit 255 (j - pos * 8) = false := by
          apply Nat.testBit_lt_two_pow
          exact lt_of_lt_of_le (show 255 < 2 ^ 8 by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
        have hb' : b.toNat.testBit (j - pos * 8) = false :=
          Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) (by omega)))
        simp [h1, h2, show ¬ j < pos * 8 by omega, this, hb', show j - 8 * pos - 8 + (8 * pos + 8) = j by omega]
  rw [key, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
theorem foldl_append_flatten : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten l (a ++ c)]
theorem drop_chunks {α : Type} (B : Nat) : ∀ (cs : List (List α)) (k : Nat),
    (cs.dropLast.all fun c => c.length == B) = true → k < cs.length →
    cs.flatten.drop (B * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = B := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == B) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show B * (k + 1) = c.length + B * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this
end ClaudeWCT.W9.Machine.VLib
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Fetch ====
section

set_option Elab.async false

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def NewCodeAt (im : Image) : Prop :=
  ∀ c, c < 169 → CodeAt im (pcOf (256 * (c + 4))) (expChunks.getD c [])
def expLook (n : Nat) : Option (BitVec 32) :=
  if 1024 ≤ n then (expChunks.getD (n / 256 - 4) [])[n % 256]? else none
set_option maxRecDepth 100000 in
theorem expChunks_length : expChunks.length = 169 := by decide +kernel
set_option maxRecDepth 100000 in
theorem expChunks_len_le : ∀ c, c < 169 → (expChunks.getD c []).length ≤ 256 := by decide +kernel
theorem expLook_ok {im : Image} (h : NewCodeAt im) : LookOK im expLook := by
  intro n w hw
  unfold expLook at hw
  split at hw
  · rename_i hn
    have hc : n / 256 - 4 < 169 := by
      by_contra hc
      rw [List.getD_eq_default _ _ (by rw [expChunks_length]; omega)] at hw
      simp at hw
    obtain ⟨h1, h2, h3, h4⟩ := h (n / 256 - 4) hc
    have hpc : (pcOf (256 * (n / 256 - 4 + 4))).toNat = 0x1000 + 4 * (256 * (n / 256)) := by
      rw [show n / 256 - 4 + 4 = n / 256 by omega, pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      have : expLook n = some w := by unfold expLook; rw [if_pos hn]; exact hw
      have hl := List.getElem?_eq_some_iff.mp hw
      have hlen : (expChunks.getD (n / 256 - 4) []).length ≤ 256 := by
        exact expChunks_len_le _ hc
      omega
    rw [hpc] at h4 h3
    obtain ⟨t, ht⟩ := h4
    have := congrArg (·[n % 256]?) ht
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hw).1, hw,
      List.getElem?_drop] at this
    rw [show 0x1000 + 4 * (256 * (n / 256)) - 0x1000 = 4 * (256 * (n / 256)) by omega,
      show 4 * (256 * (n / 256)) / 4 + n % 256 = n by omega] at this
    exact this.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_WitV5 ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.T3 (HashOutput Layer height chainCount)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_flatMap_const window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3 (LayerSignature route)
open SigGolfCandidate.T3M (layerBytes)
open ClaudeWCT.W9.T3M (headerBytes chainBytes leafBytes regionBytes)
def bcTopBlockV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  if leaf / 2 ^ (height lay - 1) % 2 = 1 then
    bytesLE 16 (ls.path (WCT9.topLevel lay)) ++ zeros 16 ++ bytesLE 4 ctr ++ zeros 28
  else zeros 32 ++ bytesLE 4 ctr ++ zeros 12 ++ bytesLE 16 (ls.path (WCT9.topLevel lay))
def layerBytesBCV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) : List UInt8 :=
  bcTopBlockV6 lay leaf ls ctr ++ (layerBytes lay leaf ls).drop 64
/-- T51: chain blocks of a staging region. The top keeps #938's 54 blocks (chain `i` at block `53 - i` below the
path blocks; the blocks of chains 51..53 are never written and stay zero). -/
def chainSlotsV6 (lay : Layer) : Nat := if lay.val = 0 then 54 else chainCount lay
theorem chainSlotsV6_lower (lay : Layer) (hl : lay.val ≠ 0) : chainSlotsV6 lay = chainCount lay := by
  simp [chainSlotsV6, hl]
theorem chainSlotsV6_ge (lay : Layer) : chainCount lay ≤ chainSlotsV6 lay := by
  fin_cases lay <;> decide
/-- T51: a staging region without its counter block. The top inserts the 3 zero blocks of #938's chains 51..53
between its 12 path blocks and its 51 chain blocks. -/
def layerBytesV6 (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) : List UInt8 :=
  if lay.val = 0 then (layerBytes lay leaf ls).take 768 ++ zeros 192 ++ (layerBytes lay leaf ls).drop 768
  else layerBytes lay leaf ls
def layerRegionV6 (N : HashOutput) (w : WCT9.Witness) (lay : Layer) : List UInt8 :=
  if lay.val = 0 then layerBytesV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
  else layerBytesBCV6 lay (route (WCT9.digestIndex N) lay).1 (w.signature.layers lay)
    (w.counters (Fin.ofNat 4 (lay.val - 1)))
/-- Staging region of the compaction pass (896 bytes). r3w (witness stack): the FTS content of the staging is dead
(the finish pass zeroes `[1152, 11000)` and rebuilds the FTS block from the signature), so only its length matters. -/
def regionBytesV6 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 896
/-- Header of the first-pass scratch layout at 0x800 (the frontier's 64-byte header: rho, digest counter, L3
counter). Machine internal; the final witness uses `ClaudeWCT.W9.T3M.headerBytes`. -/
def headerBytesV5 (w : WCT9.Witness) : List UInt8 :=
  bytesLE 16 w.signature.rho ++ bytesLE 4 w.digestCounter ++ zeros 12 ++ bytesLE 4 (w.counters 3) ++ zeros 28
theorem headerBytesV5_length (w : WCT9.Witness) : (headerBytesV5 w).length = 64 := by
  simp [headerBytesV5, zeros, bytesLE_length]
def wctBytesV6 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV6 (WCT9.child N k).val (sig.openings k)
def witListV6 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV6 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
def merkleBytesV5 (child : Nat) (op : WCT9.Opening) : List UInt8 :=
  (List.finRange 7).reverse.flatMap fun l =>
    if child / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48 else zeros 48 ++ bytesLE 16 (op.path l)
/-- Expand scratch region (1024 bytes). r3w: dead FTS content (see `regionBytesV6`); only the length matters. -/
def regionBytesV5 (_child : Nat) (_op : WCT9.Opening) : List UInt8 := zeros 1024
def wctBytesV5 (N : HashOutput) (sig : WCT9.Signature) : List UInt8 :=
  (List.finRange 9).flatMap fun k => regionBytesV5 (WCT9.child N k).val (sig.openings k)
def witListV5 (N : HashOutput) (w : WCT9.Witness) : List UInt8 :=
  headerBytesV5 w ++ wctBytesV5 N w.signature ++ zeros 8 ++ (List.finRange 4).flatMap (layerRegionV6 N w)
theorem leafBytesZ_length (op : WCT9.Opening) : (ClaudeWCT.W9.T3M.leafBytes op (zeros 16)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp [zeros])
theorem leafBytesZ_length' (op : WCT9.Opening) :
    (ClaudeWCT.W9.T3M.leafBytes op (List.replicate 16 0)).length = 128 :=
  ClaudeWCT.W9.T3M.leafBytes_length _ _ (by simp)
theorem merkleBytesV5_length (c : Nat) (op : WCT9.Opening) : (merkleBytesV5 c op).length = 448 := by
  unfold merkleBytesV5
  rw [List.length_flatMap]
  have : ∀ l : Fin 7, (if c / 2 ^ l.val % 2 = 1 then bytesLE 16 (op.path l) ++ zeros 48
      else zeros 48 ++ bytesLE 16 (op.path l)).length = 64 := fun l => by
    split <;> simp [zeros, bytesLE_length]
  simp only [this, List.map_const', List.length_reverse, List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem regionBytesV5_length (c : Nat) (op : WCT9.Opening) : (regionBytesV5 c op).length = 1024 := by
  simp only [regionBytesV5, zeros, List.length_replicate]
theorem wctBytesV5_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV5 N sig).length = 9216 := by
  unfold wctBytesV5
  rw [List.length_flatMap]
  simp only [regionBytesV5_length, List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul]
theorem bcTopBlockV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (bcTopBlockV6 lay leaf ls ctr).length = 64 := by
  unfold bcTopBlockV6; split <;> simp [zeros, bytesLE_length]
theorem height_pos (lay : Layer) : 1 ≤ height lay := by fin_cases lay <;> decide
theorem layerBytesBCV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) (ctr : BitVec 32) :
    (layerBytesBCV6 lay leaf ls ctr).length = 64 * (height lay + chainCount lay) := by
  unfold layerBytesBCV6
  rw [List.length_append, bcTopBlockV6_length, List.length_drop, SigGolfCandidate.T3M.layerBytes_length]
  have := height_pos lay
  have : 64 ≤ 64 * (height lay + chainCount lay) := by nlinarith
  omega
theorem layerBytesV6_length (lay : Layer) (leaf : Nat) (ls : LayerSignature lay) :
    (layerBytesV6 lay leaf ls).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerBytesV6 chainSlotsV6
  split
  · rename_i h
    have hl : lay = 0 := Fin.ext h
    subst hl
    have e1 : (zeros 192 : List UInt8).length = 192 := List.length_replicate ..
    have h1 : height (0 : Layer) = 12 := rfl
    have h2 : chainCount (0 : Layer) = 51 := rfl
    rw [List.length_append, List.length_append, List.length_take, List.length_drop,
      SigGolfCandidate.T3M.layerBytes_length, e1, h1, h2]
    simp
  · rw [SigGolfCandidate.T3M.layerBytes_length]
theorem layerRegionV6_length (N : HashOutput) (w : WCT9.Witness) (lay : Layer) :
    (layerRegionV6 N w lay).length = 64 * (height lay + chainSlotsV6 lay) := by
  unfold layerRegionV6; split
  · exact layerBytesV6_length _ _ _
  · rename_i h
    rw [layerBytesBCV6_length]
    simp [chainSlotsV6, h]
theorem layersV6_length (N : HashOutput) (w : WCT9.Witness) :
    ((List.finRange 4).flatMap (layerRegionV6 N w)).length = 13696 := by
  simp only [List.length_flatMap, layerRegionV6_length]
  decide

theorem witListV5_length (N : HashOutput) (w : WCT9.Witness) : (witListV5 N w).length = 22984 := by
  unfold witListV5
  simp only [List.length_append, headerBytesV5_length, wctBytesV5_length, zeros,
    List.length_replicate, layersV6_length]
theorem regionBytesV6_length (c : Nat) (op : WCT9.Opening) : (regionBytesV6 c op).length = 896 := by
  simp only [regionBytesV6, zeros, List.length_replicate]
theorem wctBytesV6_length (N : HashOutput) (sig : WCT9.Signature) : (wctBytesV6 N sig).length = 8064 := by
  unfold wctBytesV6
  rw [List.length_flatMap]
  simp only [regionBytesV6_length, List.map_const', List.length_finRange, List.sum_replicate,
    smul_eq_mul]
theorem witListV6_length (N : HashOutput) (w : WCT9.Witness) : (witListV6 N w).length = 21832 := by
  unfold witListV6
  simp only [List.length_append, headerBytesV5_length, wctBytesV6_length, zeros,
    List.length_replicate, layersV6_length]
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from T3M_Sign_Basic ====
section


section
namespace SigGolfCandidate.T3M
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def signCurrentCodeChunks : List (List (BitVec 32)) := [Images.signCode_0, Images.signCode_1, Images.signCode_2, Images.signCode_3, Images.signCode_4, Images.signCode_5, Images.signCode_6, Images.signCode_7, Images.signCode_8, Images.signCode_9, Images.signCode_10, Images.signCode_11, Images.signCode_12, Images.signCode_13, Images.signCode_14, Images.signCode_15, Images.signCode_16, Images.signCode_17, Images.signCode_18, Images.signCode_19, Images.signCode_20, Images.signCode_21, Images.signCode_22, Images.signCode_23, Images.signCode_24, Images.signCode_25, Images.signCode_26, Images.signCode_27, Images.signCode_28, Images.signCode_29, Images.signCode_30, Images.signCode_31, Images.signCode_32, Images.signCode_33, Images.signCode_34, Images.signCode_35, Images.signCode_36, Images.signCode_37, Images.signCode_38, Images.signCode_39, Images.signCode_40, Images.signCode_41, Images.signCode_42, Images.signCode_43, Images.signCode_44, Images.signCode_45, Images.signCode_46, Images.signCode_47, Images.signCode_48, Images.signCode_49, Images.signCode_50, Images.signCode_51, Images.signCode_52, Images.signCode_53, Images.signCode_54, Images.signCode_55, Images.signCode_56, Images.signCode_57, Images.signCode_58, Images.signCode_59, Images.signCode_60, Images.signCode_61, Images.signCode_62, Images.signCode_63, Images.signCode_64, Images.signCode_65, Images.signCode_66, Images.signCode_67, Images.signCode_68, Images.signCode_69, Images.signCode_70, Images.signCode_71, Images.signCode_72, Images.signCode_73, Images.signCode_74, Images.signCode_75, Images.signCode_76, Images.signCode_77, Images.signCode_78, Images.signCode_79, Images.signCode_80, Images.signCode_81, Images.signCode_82, Images.signCode_83, Images.signCode_84, Images.signCode_85]
private theorem foldl_chunks (cs : List (List (BitVec 32))) (acc : List (BitVec 32)) :
    cs.foldl (· ++ ·) acc = acc ++ cs.flatten := by
  induction cs generalizing acc with
  | nil => simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
  | cons c cs ih => simp only [List.foldl_cons, ih, List.flatten_cons, List.append_assoc]
theorem signCurrentCode_flatten : Images.signCode = signCurrentCodeChunks.flatten := by
  change signCurrentCodeChunks.foldl (· ++ ·) [] = signCurrentCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_sign_current_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (signCurrentCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.signImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.signCode.drop b).take code.length = code
  rw [signCurrentCode_flatten]
  exact h
/-- The final chunk carries the appended roots-first producer without changing old addresses. -/
private theorem signCurrentCodeChunks_prefix_length :
    (signCurrentCodeChunks.take 85).flatten.length = 21760 := by
  set_option maxRecDepth 100000 in decide +kernel

theorem signCodeTailLast_eq (b : Nat) (hlo : 21760 ≤ b) :
    Images.signCode_85.drop (b - 21760) = signCurrentCodeChunks.flatten.drop b := by
  have hs : signCurrentCodeChunks = signCurrentCodeChunks.take 85 ++ [Images.signCode_85] := by rfl
  have he : signCurrentCodeChunks.flatten.drop 21760 = Images.signCode_85 := by
    conv_lhs => rw [hs]
    rw [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← signCurrentCodeChunks_prefix_length, List.drop_left]
  rw [show b = 21760 + (b - 21760) by omega, ← List.drop_drop, he]
  simp only [Nat.add_sub_cancel_left]

theorem codeAt_sign_last {b : Nat} {code : List (BitVec 32)}
    (hlo : 21760 ≤ b) (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (hc : (Images.signCode_85.drop (b - 21760)).take code.length = code) :
    CodeAt Images.signImage (pcOf b) code := by
  apply codeAt_sign_current_slice hb
  rw [← signCodeTailLast_eq b hlo]
  exact hc

theorem codeAt_sign_shared_prefix :
    CodeAt Images.signImage (pcOf 22016) Images.signSharedPrefix := by
  apply codeAt_sign_last <;> decide +kernel

theorem codeAt_sign_shared_main :
    CodeAt Images.signImage (pcOf 22100) Images.signSharedMain := by
  apply codeAt_sign_last <;> decide +kernel

theorem codeAt_sign_shared_fts :
    CodeAt Images.signImage (pcOf 22600) Images.signSharedFts := by
  apply codeAt_sign_last <;> decide +kernel

def signCodeChunks : List (List (BitVec 32)) := [Images.signReferenceCode_0, Images.signReferenceCode_1, Images.signReferenceCode_2, Images.signReferenceCode_3, Images.signReferenceCode_4, Images.signReferenceCode_5, Images.signReferenceCode_6, Images.signReferenceCode_7, Images.signReferenceCode_8, Images.signReferenceCode_9, Images.signReferenceCode_10, Images.signReferenceCode_11, Images.signReferenceCode_12, Images.signReferenceCode_13, Images.signReferenceCode_14, Images.signReferenceCode_15, Images.signReferenceCode_16, Images.signReferenceCode_17, Images.signReferenceCode_18, Images.signReferenceCode_19, Images.signReferenceCode_20, Images.signReferenceCode_21, Images.signReferenceCode_22, Images.signReferenceCode_23, Images.signReferenceCode_24, Images.signReferenceCode_25, Images.signReferenceCode_26, Images.signReferenceCode_27, Images.signReferenceCode_28, Images.signReferenceCode_29, Images.signReferenceCode_30, Images.signReferenceCode_31, Images.signReferenceCode_32, Images.signReferenceCode_33, Images.signReferenceCode_34, Images.signReferenceCode_35, Images.signReferenceCode_36, Images.signReferenceCode_37, Images.signReferenceCode_38, Images.signReferenceCode_39, Images.signReferenceCode_40, Images.signReferenceCode_41, Images.signReferenceCode_42, Images.signReferenceCode_43, Images.signReferenceCode_44, Images.signReferenceCode_45, Images.signReferenceCode_46, Images.signReferenceCode_47, Images.signReferenceCode_48, Images.signReferenceCode_49, Images.signReferenceCode_50, Images.signReferenceCode_51, Images.signReferenceCode_52, Images.signReferenceCode_53, Images.signReferenceCode_54, Images.signReferenceCode_55, Images.signReferenceCode_56, Images.signReferenceCode_57, Images.signReferenceCode_58, Images.signReferenceCode_59, Images.signReferenceCode_60, Images.signReferenceCode_61, Images.signReferenceCode_62, Images.signReferenceCode_63, Images.signReferenceCode_64, Images.signReferenceCode_65, Images.signReferenceCode_66, Images.signReferenceCode_67, Images.signReferenceCode_68, Images.signReferenceCode_69, Images.signReferenceCode_70, Images.signReferenceCode_71, Images.signReferenceCode_72, Images.signReferenceCode_73, Images.signReferenceCode_74, Images.signReferenceCode_75, Images.signReferenceCode_76, Images.signReferenceCode_77, Images.signReferenceCode_78, Images.signReferenceCode_79, Images.signReferenceCode_80, Images.signReferenceCode_81, Images.signReferenceCode_82, Images.signReferenceCode_83, Images.signReferenceCode_84, Images.signReferenceCode_85]
theorem signCode_flatten : Images.signReferenceCode = signCodeChunks.flatten := by
  change signCodeChunks.foldl (· ++ ·) [] = signCodeChunks.flatten
  rw [foldl_chunks, List.nil_append]
theorem codeAt_sign_slice {b : Nat} {code : List (BitVec 32)}
    (hb : 0x1000 + 4 * b + 4 * code.length < 2 ^ 64)
    (h : (signCodeChunks.flatten.drop b).take code.length = code) :
    CodeAt Images.signReferenceImage (pcOf b) code := by
  apply codeAt_slice hb
  change (Images.signReferenceCode.drop b).take code.length = code
  rw [signCode_flatten]
  exact h
end SigGolfCandidate.T3M
end
section
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
def seg_0 : List (BitVec 32) := [659,528055,134967,1074728723,963331,9352067,7286819,8336419,528055,17731219,134967,1091505939,963331,9352067,7286819,8336419,784339055]
def seg_46 : List (BitVec 32) := [115]
def seg_47 : List (BitVec 32) := [134711,1041108499,134839,1074695827,930563,963459,2054362211]
def seg_54 : List (BitVec 32) := [9319171,9352067,2020810339]
def seg_57 : List (BitVec 32) := [17707779,17740675,2020808803]
def seg_60 : List (BitVec 32) := [26096387,26129283,2020807267]
def seg_63 : List (BitVec 32) := [134221459,134967,963331,9352067,7286819,8336419,150998675,134967,34541331,963331,9352067,7286819,8336419,134967,34551843,34552867,134221459,134967,135204627,963331,9352067,7286819,8336419,150998675,134967,168759059,963331,9352067,7286819,8336419,134967,135204627,34551843,34552867,1880097555,915,134711,135138835,7223331,8272931,28343,134967,202313491,1645130499,1653519235,7286819,8336419,28343,134967,219090707,1661907715,1670296451,7286819,8336419,132407,134546707,134219155,132663,268830227]
def seg_122 : List (BitVec 32) := [115]
def seg_123 : List (BitVec 32) := [134839,269389459,32567,963331,9352067,7286819,8336419,134839,269389459,134967,302976787,963331,9352067,7286819,8336419,28343,134967,336531219,1645130499,1653519235,7286819,8336419,28343,134967,353308435,1661907715,1670296451,7286819,8336419,2451]
def seg_153 : List (BitVec 32) := [412131439,1617529443]
def seg_155 : List (BitVec 32) := [4919,787,627603,134711,302910995,7223331,8272931,132407,302318867,67110291,132663,369493523]
def seg_167 : List (BitVec 32) := [115]
def seg_168 : List (BitVec 32) := [121639151]
def seg_169 : List (BitVec 32) := [431715]
def seg_170 : List (BitVec 32) := [1673619,4221562991]
def seg_172 : List (BitVec 32) := [134711,370019859,930947,34903187,34919571,134711,1426984467,10367011,196919,30775,369625107,32055,17632531,1043]
def seg_186 : List (BitVec 32) := [7340819,711218275]
def seg_188 : List (BitVec 32) := [2323]
def seg_189 : List (BitVec 32) := [4919,2147681043,241784419]
def seg_192 : List (BitVec 32) := [1667859,67310691]
def seg_194 : List (BitVec 32) := [1662483,4919,2148729619,17047315,31679283,295827,34479891,31712179,134711,7223331,8272931,4791827,263735,29754931,132407,67110291]
def seg_210 : List (BitVec 32) := [115]
def seg_211 : List (BitVec 32) := [4791827,265911,31329843,134967,772738835,930563,9319299,7286819,8336419,4919,2417165075,17047315,31679283,1196429423]
def seg_225 : List (BitVec 32) := [33857299,31679283,134711,739118611,7223331,8272931,132407,738526483,67110291,132663,805701139]
def seg_236 : List (BitVec 32) := [115]
def seg_237 : List (BitVec 32) := [7735,2148404755,19795507,5119507,3018291,134839,806260371,963331,9352067,7221283,8270883,1640723,4045402223]
def seg_250 : List (BitVec 32) := [11536275,6839,2686093971,17047315,32172723,1506803951]
def seg_256 : List (BitVec 32) := [4461331,3412883,7537459,134327,1242336403,7113907,2451]
def seg_263 : List (BitVec 32) := [3146515,40492131]
def seg_265 : List (BitVec 32) := [3773203,26411827,209667,4395795,263095,7540275,930563,9319299,7155747,8205347,17632531,1673619,4238340207]
def seg_278 : List (BitVec 32) := [7342995,2451]
def seg_280 : List (BitVec 32) := [3146515,208262243]
def seg_282 : List (BitVec 32) := [3773203,26411827,211459,5047,2147713939,7998003,2707,2098067,7965283]
def seg_291 : List (BitVec 32) := [8600195,5047,2147713939,8030899]
def seg_295 : List (BitVec 32) := [756499]
def seg_296 : List (BitVec 32) := [34278499]
def seg_297 : List (BitVec 32) := [4294642451,23745331,1274771,4261644515]
def seg_301 : List (BitVec 32) := [1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,4242534511]
def seg_310 : List (BitVec 32) := [2835]
def seg_311 : List (BitVec 32) := [7340819,74141795]
def seg_313 : List (BitVec 32) := [23745331,1274771,33789539]
def seg_316 : List (BitVec 32) := [1262355,23778227,40076387]
def seg_319 : List (BitVec 32) := [4398611,3018291,930563,9319299,6828067,7877667,17303571]
def seg_326 : List (BitVec 32) := [1772307,4229951599]
def seg_328 : List (BitVec 32) := [723859,1673619,4087345263]
def seg_331 : List (BitVec 32) := [7342867]
def seg_332 : List (BitVec 32) := [11535123,40589411]
def seg_334 : List (BitVec 32) := [23745331,1262355,4398611,3018291,930563,9319299,6828067,7877667,17303571,1772307,4246728815]
def seg_345 : List (BitVec 32) := [4464147,263267]
def seg_347 : List (BitVec 32) := [17698323]
def seg_348 : List (BitVec 32) := [134839,839814803,31329843,16855811,25244547,7221283,8270883,1311763,3584028783]
def seg_357 : List (BitVec 32) := [4919,2954035987,295827,134711,839781907,7223331,8272931,132407,839189779,134219155,132663,973473299]
def seg_369 : List (BitVec 32) := [115]
def seg_370 : List (BitVec 32) := [134839,974032531,134967,638521107,963331,9352067,7286819,8336419,135479,3987,45092115,3475,3146771,6293395,34871,772278291,211814547,134711,1426984467,930563,218003,66063891,29620531,591635,6509715,1052770543]
def seg_396 : List (BitVec 32) := [1112539375]
def seg_397 : List (BitVec 32) := [2098195,6293395,34871,4245162003,211814547,134711,1426984467,930563,6509459,66063891,29620531,591635,12801171,989855983]
def seg_411 : List (BitVec 32) := [1049624815]
def seg_412 : List (BitVec 32) := [1049619,7341971,34871,3406301203,210765971,134711,1426984467,930563,12800915,133172755,29620531,591635,20141203,926941423]
def seg_426 : List (BitVec 32) := [986710255]
def seg_427 : List (BitVec 32) := [1043,1171,56626451,53480851,152045715,134711,1426984467,930563,20140947,7735,4294839827,29620531,591635,864026863]
def seg_441 : List (BitVec 32) := [1052563,133943,1108019987,35767,2299235219,344981743]
def seg_447 : List (BitVec 32) := [1989148783]
def seg_456 : List (BitVec 32) := [1530131,1657107,1644819,138167,2685111187,134327,537693331,273678575]
def seg_464 : List (BitVec 32) := [1640723,138167,2685111187,134327,588024979,248512751]
def seg_470 : List (BitVec 32) := [1662483,5047,2147713939,8261171,806355731,918419,134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
def seg_485 : List (BitVec 32) := [115]
def seg_486 : List (BitVec 32) := [134839,604933779,36663,3289321235,963331,9352067,7286819,8336419,2099987,35895,3305901075,1073744403]
def seg_498 : List (BitVec 32) := [12583699,174805603]
def seg_500 : List (BitVec 32) := [23551539,1986067,4919,3490906899,34283283,31679283,34476947,134711,7223331,8272931,132407,67110291,132663,101058067]
def seg_514 : List (BitVec 32) := [115]
def seg_515 : List (BitVec 32) := [23548723,1262355,5047,2147713939,7537459,1711635,1103299379,4395795,37815,33784723,7537459,209795,8601091,134839,101617299,963331,9354883,6538163,31346227,8138787,30159907,17566739,1726995,1772307,4125093999]
def seg_540 : List (BitVec 32) := [932261999,1299]
def seg_542 : List (BitVec 32) := [115]
def seg_1173 : List (BitVec 32) := [33299,1683]
def seg_1175 : List (BitVec 32) := [1049363,15930163,73846883]
def seg_1178 : List (BitVec 32) := [428307,133943,1175128851,138167,2685111187,15112291]
def seg_1184 : List (BitVec 32) := [133943,1108019987,527251]
def seg_1187 : List (BitVec 32) := [13829043,4428691,2329779,3667914991]
def seg_1191 : List (BitVec 32) := [1476243,4225757295]
def seg_1193 : List (BitVec 32) := [1463812207,19,4007653615]
def seg_1196 : List (BitVec 32) := [1683,1049363,15930163,14879155,5051283,7867443]
def seg_1202 : List (BitVec 32) := [49731683]
def seg_1203 : List (BitVec 32) := [14278195,1986067,5119507,3018291,930563,9319299,7090211,8139811,17566739,1476243,4250923119]
def seg_1214 : List (BitVec 32) := [134967,638521107,210800751,25244547,7286819,8336419,131175]
def seg_543 : List (BitVec 32) := [1049235,1049875]
def seg_545 : List (BitVec 32) := [115]
def ker_546 : List (BitVec 32) := [22022803,2579,134327,0x4a0c8c93,7340819,376066659,5903123,3806099,0x40730333,21168947,32703251,6509459,3380115,134711,370019859,29590451,245251,8633987,66286355,7233075,2006675,66061203,0x406383b3,8298163,31354419,33555383,0xfff38393,8289843,0xfe7313,7541523,5135123,0x7fb7b13,0xbe5b93,0x7fbfb93,19815443,0x7fc7c13,23844963,721811,756499,232339,24926307,754579,789395,232467,23844963,721811,756499,232339,0xd7b0463,0xd8b8263,24855475,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,25936819,8392211,2342547,0x41de0e33,4439699,0x41de0e33,8634003,0x41de0e33,17022611,0x41de0e33,33799827,0x41de0e33,67354259,0x41de0e33,0x803be93,0x41de0e33,30050995,4885139,23266227,8171555,24314803,8172579,25363379,8173603,25988243,1706515,0xe9dff06f,0x7400313,7001699,1050259,32871,1683,32871,0x5790006f,0x6911306f,19,19,19,19,19,19,19,2451,617689199,0x4c698c63,134711,638455315,54403107,132407,637863187,67110291,132663,705037843,115,134711,705564179,930563,9319299,3219,0x540406e3,0x4851306f,0x540e5263,7568915,30182579,3366419,8289811,30182579,6512147,8289811,30182579,9657875,8289811,30182579,0xc35e13,8289811,30182579,0xf35e13,8289811,30182579,19095059,8289811,30182579,22240787,8289811,30182579,25386515,8289811,30182579,28532243,8289811,30182579,31677971,8289811,30182579,34823699,8289811,30182579,37969427,8289811,30182579,41115155,8289811,30182579,44260883,8289811,30182579,47406611,8289811,30182579,50552339,8289811,30182579,53698067,8289811,30182579,56843795,8289811,30182579,59989523,8289811,30182579,63135251,8289811,30182579,7601683,30182579,3399187,8289811,30182579,6544915,8289811,30182579,9690643,8289811,30182579,0xc3de13,8289811,30182579,0xf3de13,8289811,30182579,19127827,8289811,30182579,22273555,8289811,30182579,25419283,8289811,30182579,28565011,8289811,30182579,31710739,8289811,30182579,34856467,8289811,30182579,38002195,8289811,30182579,41147923,8289811,30182579,44293651,8289811,30182579,47439379,8289811,30182579,50585107,8289811,30182579,53730835,8289811,30182579,56876563,8289811,30182579,60022291,8289811,30182579,63168019,8289811,30182579,0x41988e33,8392339,903771235,0x10d1306f,19,19,19,0x13,0x13,0xffff37,200211,0x7fe7e93,32411315,969859,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,1285779,30338611,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7fe7e93,32411315,970371,31231155,8281619,0x7e7e93,31231155,0x3e5e93,0x7efe93,31231155,0x3d3de93,31231155,0x411c8eb3,0xbe0e9ee3,0x7591306f,133815,0x420a8a93,0x80f0f13,0x7f37e13,3022355,32378419,945795,31096867,9363091,31096995,9363091,31097123,7557907,60005907,29582131,7590803,3836563,1706515,18497043,0xfc0e10e3,0x737e13,0x1ca8123,0x335313,0x737e13,0x1ca8023,0x335313,0x737e13,0x1ca80a3,0x8067,197907,230803,1555,17828371,0x7f57e13,3022355,32378419,0x83e4e03,29754931,7689491,60136979,29713715,7722387,0xfffa0a13,0xfc0a1ce3,0x757e13,0xffae0e13,1981971,29754931,0x355513,0x757e13,0xffae0e13,1981971,29754931,0x355513,0xffa50e13,1981971,29754931,9846291,0xa0e1e63,2579,0xf11ff06f,0x960410e3,0xffff37,662654467,0x940e0ae3,663696131,672084867,0x8100c93,2579,0xeedff06f,1281555,66985491,29573939,1282963,2347923,854675,263267,0xfffd0a93,2579,89806435,7343635,3149459,28989027,3149331,2100883,29589299,134711,0x420e0e13,21892659,32374819,30626611,67112467,0x41de0e33,29597235,29582131,30659507,1706515,0xfb9ff06f,265315,0x41988e33,134839,0x420e8e93,22974131,30310435,0x8067,1673619,0x4bc1306f]
def seg_1221 : List (BitVec 32) := [131895,394474243,14897939,7566099,3993179747,3591368815]
def seg_17 : List (BitVec 32) := [40759,4262399763,963331,9352067,7286819,8336419,150998675,40759,963331,9352067,7286819,8336419,40759,4262399763,34551843,34552867,4919,3759342355,915,40503,4262333971,7223331,8272931,38199,4261741843,34231,67470739,132663,1040582163]
def seg_448 : List (BitVec 32) := [133943,1175128851,138167,2685111187,36023,3272379539,1526035,307233007]
def seg_1227 : List (BitVec 32) := [134711,921107,3767,135171731,963331,7221283,9351939,7222307,17740547,40775715,26129155,40776739,34486307,34487331,4919,3759342355,7223331,932899,132407,328979,67110291,460343,394771,115,1049363,33755923,7224355,460343,33949203,115,4293921043,3758355,657847,625043,461623,723731,134327,1041009811,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15511587,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15512611,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15513635,17500947,736131,19659699,9124867,526007,33982099,1811,452483,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,4646787,15173555,58177587,58165171,3676179,64477331,18352179,19396531,16255027,64509715,19429427,17237811,8816275,4181106403,64444307,19363635,16189235,19351475,1554323,4294412179,16217907,25626419,15514659]
def seg_1432 : List (BitVec 32) := [2782912623]
def seg_1433 : List (BitVec 32) := [2835,35895,3205237779,6711,657939]
def seg_1438 : List (BitVec 32) := [23551539,1986067,920467,4919,3490906899,34280339,7562035,1823635,33788819,134711,921107,7223331,8272931,132407,328979,67110291,132663,101058067]
def seg_1456 : List (BitVec 32) := [115]
def seg_1457 : List (BitVec 32) := [11831,921107,1711763,1105071667,25038387,5119507,528055,34508435,31329843,1834643,5152403,13536947,930563,963459,7553843,7090211,9319171,9352067,7553843,7091235,17566739,1726995,1772307,12583699,4100680419]
def seg_1482 : List (BitVec 32) := [2492461167]
def kerCode : List (BitVec 32) := seg_543 ++ seg_545 ++ ker_546
/-- Campaign T8D (NF17): the sign's max-digit selector at 2013 (`li s5,7; bge s3,s11; li s5,4; j`): top chains
`< 51` have maximum digit 4, chains 51..53 (radix 8) maximum digit 7. The keygen keeps its own `Keygen.maxLow`. -/
def maxLowS : List (BitVec 32) := [0x700a93,0x99b9d663]
def maxLayoutS : Rv.Layout := [(0, maxLowS), (2, Keygen.maxHigh)]
def maxDigitCodeS : List (BitVec 32) := layoutCode maxLayoutS
theorem maxLayoutS_ok : layoutOk 0 maxLayoutS = true := by decide +kernel
def seg_2045 : List (BitVec 32) := [1074332563,1073972115,267648787,9379603,8639379,31712179,7735,4043181587,29622067,5185299,4445075,29619123,31712179,15927,859704851,29622067,3088147,2347923,29619123,31712179,24119,1432227347,29622067,2039571,1299347,29619123,31712179,50566035,2987384943]
def seg_1483 : List (BitVec 32) := Keygen.packedHelper ++ List.drop 25 [0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013, 0x00000013]
def signL : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, seg_543), (545, seg_545), (546, ker_546), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, maxDigitCodeS), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signL_ok : layoutOk 0 signL = true := by decide +kernel
abbrev image : Image := Images.signReferenceImage
theorem codeAt_0 : CodeAt image (pcOf 0) seg_0 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_46 : CodeAt image (pcOf 46) seg_46 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_47 : CodeAt image (pcOf 47) seg_47 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_54 : CodeAt image (pcOf 54) seg_54 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_57 : CodeAt image (pcOf 57) seg_57 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_60 : CodeAt image (pcOf 60) seg_60 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_63 : CodeAt image (pcOf 63) seg_63 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_122 : CodeAt image (pcOf 122) seg_122 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_123 : CodeAt image (pcOf 123) seg_123 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_155 : CodeAt image (pcOf 155) seg_155 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_167 : CodeAt image (pcOf 167) seg_167 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_168 : CodeAt image (pcOf 168) seg_168 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_169 : CodeAt image (pcOf 169) seg_169 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_170 : CodeAt image (pcOf 170) seg_170 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_172 : CodeAt image (pcOf 172) seg_172 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_186 : CodeAt image (pcOf 186) seg_186 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_188 : CodeAt image (pcOf 188) seg_188 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_189 : CodeAt image (pcOf 189) seg_189 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_192 : CodeAt image (pcOf 192) seg_192 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_194 : CodeAt image (pcOf 194) seg_194 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_210 : CodeAt image (pcOf 210) seg_210 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_211 : CodeAt image (pcOf 211) seg_211 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_236 : CodeAt image (pcOf 236) seg_236 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_237 : CodeAt image (pcOf 237) seg_237 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_250 : CodeAt image (pcOf 250) seg_250 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_256 : CodeAt image (pcOf 256) seg_256 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_263 : CodeAt image (pcOf 263) seg_263 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_265 : CodeAt image (pcOf 265) seg_265 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_278 : CodeAt image (pcOf 278) seg_278 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_280 : CodeAt image (pcOf 280) seg_280 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_282 : CodeAt image (pcOf 282) seg_282 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_291 : CodeAt image (pcOf 291) seg_291 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_295 : CodeAt image (pcOf 295) seg_295 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_296 : CodeAt image (pcOf 296) seg_296 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_297 : CodeAt image (pcOf 297) seg_297 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_301 : CodeAt image (pcOf 301) seg_301 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_310 : CodeAt image (pcOf 310) seg_310 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_311 : CodeAt image (pcOf 311) seg_311 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_313 : CodeAt image (pcOf 313) seg_313 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_316 : CodeAt image (pcOf 316) seg_316 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_319 : CodeAt image (pcOf 319) seg_319 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_326 : CodeAt image (pcOf 326) seg_326 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_328 : CodeAt image (pcOf 328) seg_328 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_331 : CodeAt image (pcOf 331) seg_331 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_332 : CodeAt image (pcOf 332) seg_332 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_334 : CodeAt image (pcOf 334) seg_334 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_345 : CodeAt image (pcOf 345) seg_345 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_347 : CodeAt image (pcOf 347) seg_347 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_348 : CodeAt image (pcOf 348) seg_348 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_357 : CodeAt image (pcOf 357) seg_357 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_369 : CodeAt image (pcOf 369) seg_369 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_370 : CodeAt image (pcOf 370) seg_370 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_396 : CodeAt image (pcOf 396) seg_396 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_397 : CodeAt image (pcOf 397) seg_397 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_411 : CodeAt image (pcOf 411) seg_411 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_412 : CodeAt image (pcOf 412) seg_412 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_426 : CodeAt image (pcOf 426) seg_426 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_427 : CodeAt image (pcOf 427) seg_427 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_441 : CodeAt image (pcOf 441) seg_441 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_447 : CodeAt image (pcOf 447) seg_447 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_456 : CodeAt image (pcOf 456) seg_456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_464 : CodeAt image (pcOf 464) seg_464 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_470 : CodeAt image (pcOf 470) seg_470 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_485 : CodeAt image (pcOf 485) seg_485 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_486 : CodeAt image (pcOf 486) seg_486 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_498 : CodeAt image (pcOf 498) seg_498 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_500 : CodeAt image (pcOf 500) seg_500 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_514 : CodeAt image (pcOf 514) seg_514 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_515 : CodeAt image (pcOf 515) seg_515 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_542 : CodeAt image (pcOf 542) seg_542 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_543 : CodeAt image (pcOf 543) seg_543 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_545 : CodeAt image (pcOf 545) seg_545 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1173 : CodeAt image (pcOf 1173) seg_1173 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1175 : CodeAt image (pcOf 1175) seg_1175 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1178 : CodeAt image (pcOf 1178) seg_1178 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1184 : CodeAt image (pcOf 1184) seg_1184 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1187 : CodeAt image (pcOf 1187) seg_1187 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1191 : CodeAt image (pcOf 1191) seg_1191 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1193 : CodeAt image (pcOf 1193) seg_1193 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1196 : CodeAt image (pcOf 1196) seg_1196 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1202 : CodeAt image (pcOf 1202) seg_1202 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1203 : CodeAt image (pcOf 1203) seg_1203 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_17 : CodeAt image (pcOf 17) seg_17 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_448 : CodeAt image (pcOf 448) seg_448 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1227 : CodeAt image (pcOf 1227) seg_1227 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1432 : CodeAt image (pcOf 1432) seg_1432 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1433 : CodeAt image (pcOf 1433) seg_1433 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1438 : CodeAt image (pcOf 1438) seg_1438 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1456 : CodeAt image (pcOf 1456) seg_1456 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1457 : CodeAt image (pcOf 1457) seg_1457 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_1482 : CodeAt image (pcOf 1482) seg_1482 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_maxDigit : CodeAt image (pcOf 2013) maxDigitCodeS :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2017 : CodeAt image (pcOf 2017) Keygen.revCode :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_225 : CodeAt image (pcOf 225) seg_225 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
theorem codeAt_2045 : CodeAt image (pcOf 2045) seg_2045 :=
  codeAt_sign_slice (by decide +kernel) (by decide +kernel)
def signK : Rv.Layout := [(0, seg_0), (17, seg_17), (46, seg_46), (47, seg_47), (54, seg_54), (57, seg_57), (60, seg_60), (63, seg_63), (122, seg_122), (123, seg_123), (153, seg_153), (155, seg_155), (167, seg_167), (168, seg_168), (169, seg_169), (170, seg_170), (172, seg_172), (186, seg_186), (188, seg_188), (189, seg_189), (192, seg_192), (194, seg_194), (210, seg_210), (211, seg_211), (225, seg_225), (236, seg_236), (237, seg_237), (250, seg_250), (256, seg_256), (263, seg_263), (265, seg_265), (278, seg_278), (280, seg_280), (282, seg_282), (291, seg_291), (295, seg_295), (296, seg_296), (297, seg_297), (301, seg_301), (310, seg_310), (311, seg_311), (313, seg_313), (316, seg_316), (319, seg_319), (326, seg_326), (328, seg_328), (331, seg_331), (332, seg_332), (334, seg_334), (345, seg_345), (347, seg_347), (348, seg_348), (357, seg_357), (369, seg_369), (370, seg_370), (396, seg_396), (397, seg_397), (411, seg_411), (412, seg_412), (426, seg_426), (427, seg_427), (441, seg_441), (447, seg_447), (448, seg_448), (456, seg_456), (464, seg_464), (470, seg_470), (485, seg_485), (486, seg_486), (498, seg_498), (500, seg_500), (514, seg_514), (515, seg_515), (540, seg_540), (542, seg_542), (543, kerCode), (1013, Keygen.subCode), (1173, seg_1173), (1175, seg_1175), (1178, seg_1178), (1184, seg_1184), (1187, seg_1187), (1191, seg_1191), (1193, seg_1193), (1196, seg_1196), (1202, seg_1202), (1203, seg_1203), (1214, seg_1214), (1221, seg_1221), (1227, seg_1227), (1432, seg_1432), (1433, seg_1433), (1438, seg_1438), (1456, seg_1456), (1457, seg_1457), (1482, seg_1482), (1483, seg_1483), (2013, maxDigitCodeS), (2017, Keygen.revCode), (2045, seg_2045)]
theorem signK_ok : layoutOk 0 signK = true := by decide +kernel
sym_block blk_0 := symRun { noAlias := true } seg_0 (pcOf 0) 100
sym_block blk_47 := symRun { noAlias := true } seg_47 (pcOf 47) 100
sym_block blk_54 := symRun { noAlias := true } seg_54 (pcOf 54) 100
sym_block blk_57 := symRun { noAlias := true } seg_57 (pcOf 57) 100
sym_block blk_60 := symRun { noAlias := true } seg_60 (pcOf 60) 100
sym_block blk_63 := symRun { noAlias := true } seg_63 (pcOf 63) 100
sym_block blk_123 := symRun { noAlias := true } seg_123 (pcOf 123) 100
sym_block blk_153 := symRun { noAlias := true } seg_153 (pcOf 153) 100
sym_block blk_155 := symRun { noAlias := true } seg_155 (pcOf 155) 100
sym_block blk_168 := symRun { noAlias := true } seg_168 (pcOf 168) 100
sym_block blk_169 := symRun { noAlias := true } seg_169 (pcOf 169) 100
sym_block blk_170 := symRun { noAlias := true } seg_170 (pcOf 170) 100
sym_block blk_172 := symRun { noAlias := true } seg_172 (pcOf 172) 100
sym_block blk_186 := symRun { noAlias := true } seg_186 (pcOf 186) 100
sym_block blk_188 := symRun { noAlias := true } seg_188 (pcOf 188) 100
sym_block blk_189 := symRun { noAlias := true } seg_189 (pcOf 189) 100
sym_block blk_192 := symRun { noAlias := true } seg_192 (pcOf 192) 100
sym_block blk_194 := symRun { noAlias := true } seg_194 (pcOf 194) 100
sym_block blk_211 := symRun { noAlias := true } seg_211 (pcOf 211) 100
sym_block blk_225 := symRun { noAlias := true } seg_225 (pcOf 225) 100
sym_block blk_2045 := symRun { noAlias := true } seg_2045 (pcOf 2045) 100
sym_block blk_237 := symRun { noAlias := true } seg_237 (pcOf 237) 100
sym_block blk_250 := symRun { noAlias := true } seg_250 (pcOf 250) 100
sym_block blk_256 := symRun { noAlias := true } seg_256 (pcOf 256) 100
sym_block blk_263 := symRun { noAlias := true } seg_263 (pcOf 263) 100
sym_block blk_265 := symRun { noAlias := true } seg_265 (pcOf 265) 100
sym_block blk_278 := symRun { noAlias := true } seg_278 (pcOf 278) 100
sym_block blk_280 := symRun { noAlias := true } seg_280 (pcOf 280) 100
sym_block blk_282 := symRun { noAlias := true } seg_282 (pcOf 282) 100
sym_block blk_291 := symRun { noAlias := true } seg_291 (pcOf 291) 100
sym_block blk_295 := symRun { noAlias := true } seg_295 (pcOf 295) 100
sym_block blk_296 := symRun { noAlias := true } seg_296 (pcOf 296) 100
sym_block blk_297 := symRun { noAlias := true } seg_297 (pcOf 297) 100
sym_block blk_301 := symRun { noAlias := true } seg_301 (pcOf 301) 100
sym_block blk_310 := symRun { noAlias := true } seg_310 (pcOf 310) 100
sym_block blk_311 := symRun { noAlias := true } seg_311 (pcOf 311) 100
sym_block blk_313 := symRun { noAlias := true } seg_313 (pcOf 313) 100
sym_block blk_316 := symRun { noAlias := true } seg_316 (pcOf 316) 100
sym_block blk_319 := symRun { noAlias := true } seg_319 (pcOf 319) 100
sym_block blk_326 := symRun { noAlias := true } seg_326 (pcOf 326) 100
sym_block blk_328 := symRun { noAlias := true } seg_328 (pcOf 328) 100
sym_block blk_331 := symRun { noAlias := true } seg_331 (pcOf 331) 100
sym_block blk_332 := symRun { noAlias := true } seg_332 (pcOf 332) 100
sym_block blk_334 := symRun { noAlias := true } seg_334 (pcOf 334) 100
sym_block blk_345 := symRun { noAlias := true } seg_345 (pcOf 345) 100
sym_block blk_347 := symRun { noAlias := true } seg_347 (pcOf 347) 100
sym_block blk_348 := symRun { noAlias := true } seg_348 (pcOf 348) 100
sym_block blk_357 := symRun { noAlias := true } seg_357 (pcOf 357) 100
sym_block blk_370 := symRun { noAlias := true } seg_370 (pcOf 370) 100
sym_block blk_396 := symRun { noAlias := true } seg_396 (pcOf 396) 100
sym_block blk_397 := symRun { noAlias := true } seg_397 (pcOf 397) 100
sym_block blk_411 := symRun { noAlias := true } seg_411 (pcOf 411) 100
sym_block blk_412 := symRun { noAlias := true } seg_412 (pcOf 412) 100
sym_block blk_426 := symRun { noAlias := true } seg_426 (pcOf 426) 100
sym_block blk_427 := symRun { noAlias := true } seg_427 (pcOf 427) 100
sym_block blk_441 := symRun { noAlias := true } seg_441 (pcOf 441) 100
sym_block blk_447 := symRun { noAlias := true } seg_447 (pcOf 447) 100
sym_block blk_456 := symRun { noAlias := true } seg_456 (pcOf 456) 100
sym_block blk_464 := symRun { noAlias := true } seg_464 (pcOf 464) 100
sym_block blk_470 := symRun { noAlias := true } seg_470 (pcOf 470) 100
sym_block blk_486 := symRun { noAlias := true } seg_486 (pcOf 486) 100
sym_block blk_498 := symRun { noAlias := true } seg_498 (pcOf 498) 100
sym_block blk_500 := symRun { noAlias := true } seg_500 (pcOf 500) 100
sym_block blk_515 := symRun { noAlias := true } seg_515 (pcOf 515) 100
sym_block blk_540 := symRun { noAlias := true } seg_540 (pcOf 540) 100
sym_block blk_1173 := symRun { noAlias := true } seg_1173 (pcOf 1173) 100
sym_block blk_1175 := symRun { noAlias := true } seg_1175 (pcOf 1175) 100
sym_block blk_1178 := symRun { noAlias := true } seg_1178 (pcOf 1178) 100
sym_block blk_1184 := symRun { noAlias := true } seg_1184 (pcOf 1184) 100
sym_block blk_1187 := symRun { noAlias := true } seg_1187 (pcOf 1187) 100
sym_block blk_1191 := symRun { noAlias := true } seg_1191 (pcOf 1191) 100
sym_block blk_1193 := symRun { noAlias := true } seg_1193 (pcOf 1193) 100
sym_block blk_1196 := symRun { noAlias := true } seg_1196 (pcOf 1196) 100
sym_block blk_1202 := symRun { noAlias := true } seg_1202 (pcOf 1202) 100
sym_block blk_1203 := symRun { noAlias := true } seg_1203 (pcOf 1203) 100
sym_block blk_1214 := symRun { noAlias := true } seg_1214 (pcOf 1214) 100
sym_block blk_543 := symRun { noAlias := true } seg_543 (pcOf 543) 100
sym_block blk_1432 := symRun { noAlias := true } seg_1432 (pcOf 1432) 100
sym_block blk_1433 := symRun { noAlias := true } seg_1433 (pcOf 1433) 100
sym_block blk_1438 := symRun { noAlias := true } seg_1438 (pcOf 1438) 100
sym_block blk_1457 := symRun { noAlias := true } seg_1457 (pcOf 1457) 100
sym_block blk_1482 := symRun { noAlias := true } seg_1482 (pcOf 1482) 100
end SigGolfCandidate.T3M.Sign
end
section
abbrev SigGolfCandidate.T3M.Keygen.MACBLK : Nat := 0x8FE0
namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (M Spec publicHash shortHash privateHash privatePair privateMac privateNonce mask
  privateInput header pad64 Coordinate HashOutput Digest Region)
open SigGolfCandidate.T3M.Keygen (PRIV SEEDS CHAIN NODE NOUT LOUT LEAFPK MOUT ZDIG DUMMY TOP MACBLK REGION)
open SphincsSecurity (bytesLE bytesLE_length)
abbrev MSG : Nat := 0x6620
abbrev SK : Nat := 0x80
abbrev SIG : Nat := 0x7000
abbrev CACHE : Nat := 0x80000
abbrev NONCE : Nat := 0x20080
abbrev RHOOUT : Nat := 0x20100
abbrev DIG : Nat := 0x20120
abbrev NBUF : Nat := 0x20160
abbrev ENC : Nat := 0x20260
abbrev EOUT : Nat := 0x202A0
abbrev FLEAF : Nat := 0x202C0
abbrev LFOUT : Nat := 0x20300
abbrev FOREST : Nat := 0x20320
abbrev FOUT : Nat := 0x203A0
abbrev MACOUT : Nat := 0x203E0
abbrev TAG : Nat := 0x20400
abbrev DIGITS : Nat := 0x20420
abbrev SEL : Nat := 0x204A0
abbrev IDXV : Nat := 0x20550
abbrev LOW : Nat := 0x21000
abbrev FTS : Nat := 0x30000
abbrev SEC : Nat := 0x40000
macro "sg_omega" : tactic =>
  `(tactic| ((try simp only [PRIV, SEEDS, CHAIN, NODE, NOUT, LOUT, LEAFPK, MOUT, ZDIG, DUMMY, TOP, MACBLK,
    REGION, MSG, SK, SIG, CACHE, NONCE, RHOOUT, DIG, NBUF, ENC, EOUT, FLEAF, LFOUT, FOREST, FOUT, MACOUT, TAG,
    DIGITS, SEL, IDXV, LOW, FTS, SEC] at *); omega))
section tb
variable {α β : Type} {image : Image} {sk : BitVec 256}
theorem TBSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem TBSim.of_eq {s : MachineState} {W W' : Nat} {p q : M α} {Q : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (he : p = q) (hW : W = W') : TBSim image sk s W' q Q := by
  subst he hW; exact h
theorem TBSim.post_steps {s : MachineState} {W k c : Nat} {p : M α} {Q Q' : α → MachineState → Prop}
    (h : TBSim image sk s W p Q) (hs : ∀ a t, Q a t → ∃ u, Steps image t k c u ∧ Q' a u) :
    TBSim image sk s (W + c) p Q' :=
  TBSim.of_eq (TBSim.bind (f := fun a => (Pure.pure a : M α)) h
    (fun a t ht => by obtain ⟨u, hu, hq⟩ := hs a t ht; exact TBSim.pure_steps hu hq)) (bind_pure p) rfl
theorem TBSim.publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.shortHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (pad64 input)).blocks + W) (shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem TBSim.privateHash_bind {s : MachineState} {co : Coordinate} {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk co))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (privateInput sk co)).blocks + W) (privateHash co >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_privateHash]
  exact Sim.query_bind hf ht0 hv hq h
theorem TBSim.privateNonce_bind {s : MachineState} {m : T3.Message} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (privateInput sk (.inr (.inl m))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * 2 + W) (privateNonce m >>= f) Q := by
  have hb : (toQ (privateInput sk (.inr (.inl m)))).blocks = 2 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_nonce_eq]
    simp [bytesLE_length, SigGolfCandidate.T3.zero16]
  have : privateNonce m >>= f = privateHash (.inr (.inl m)) >>= fun a => f (a.extractLsb' 0 128) := by
    unfold privateNonce; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.privatePair_bind {s : MachineState} {tag lay tree position index : Nat} {W : Nat}
    {f : Digest × Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header tag lay tree position index))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (a.extractLsb' 0 128, a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (privatePair tag lay tree position index >>= f) Q := by
  have hb : (toQ (privateInput sk (.inl (header tag lay tree position index)))).blocks = 1 := by
    rw [blocks_toQ (privateInput_aligned _ _), privateInput_tweak_length]
  have : privatePair tag lay tree position index >>= f =
      privateHash (.inl (header tag lay tree position index)) >>= fun a =>
        f (a.extractLsb' 0 128, a.extractLsb' 128 128) := by
    unfold privatePair; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.of_eq (TBSim.privateHash_bind hf ht0 hv hq h) rfl (by rw [hb])
theorem TBSim.mask_bind {s : MachineState} {level index : Nat} {W : Nat}
    {f : Digest → M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true)
    (hq : hashInput s = toQ (privateInput sk (.inl (header 13 0 0 level (index/2)))))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W
      (f (if index % 2 = 0 then a.extractLsb' 0 128 else a.extractLsb' 128 128)) Q) :
    TBSim image sk s (8 + W) (mask level index >>= f) Q := by
  have : mask level index >>= f = privatePair 13 0 0 level (index/2) >>=
      fun x => f (if index % 2 = 0 then x.1 else x.2) := by
    unfold mask T3.pairedMask; rw [bind_assoc]; simp only [pure_bind]
  rw [this]
  exact TBSim.privatePair_bind hf ht0 hv hq h
end tb
structure Failed (t : MachineState) : Prop where
  pc : t.pc = pcOf 545
  x5 : t.getReg .x5 = 1
  x10 : t.getReg .x10 = 1
theorem fetch_545 (s : MachineState) (hpc : s.pc = pcOf 545) : fetch image s = some (.base .ECALL) :=
  (codeAt_545.fetch s hpc).trans rfl
theorem fail_spec (s : MachineState) (hpc : s.pc = pcOf 543) :
    ∃ t, Steps image s 2 2 t ∧ Failed t ∧ RegsExcept s t [.x5, .x10] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blk_543 codeAt_543 s hpc (by simp [blk_543.res, rv_simp]), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · simp [blk_543.res, E.eval]
  · simp [blk_543.res, rv_simp]
  · simp [blk_543.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blk_543.res, rv_simp] <;> rfl
  · intro A _ _; simp [blk_543.res, rv_simp]
theorem bv256_eq_iff (x y : BitVec 256) :
    x = y ↔ (x.extractLsb' 0 64 = y.extractLsb' 0 64 ∧ x.extractLsb' 64 64 = y.extractLsb' 64 64 ∧
      x.extractLsb' 128 64 = y.extractLsb' 128 64 ∧ x.extractLsb' 192 64 = y.extractLsb' 192 64) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    apply BitVec.eq_of_toNat_eq
    have e0 := congrArg BitVec.toNat h0; have e1 := congrArg BitVec.toNat h1
    have e2 := congrArg BitVec.toNat h2; have e3 := congrArg BitVec.toNat h3
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at e0 e1 e2 e3
    have hx := x.isLt; have hy := y.isLt
    simp only [Nat.reducePow] at e0 e1 e2 e3 hx hy
    omega
theorem bytesToWordLE_bytes {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j + 8 ≤ n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply Keygen.word_ext_bytes
  intro i hi
  rw [Keygen.extractByte_bytesToWordLE _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [Keygen.extractByte_toNat']
  simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
    List.getElem?_map, List.getElem?_range (show 8 * j + i < n by omega), if_pos hi, Option.map_some,
    Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * j) = y
  interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
end SigGolfCandidate.T3M.Sign
end
end
-- ==== merged from T3M_Expand_PackedHeader ====
section

namespace SigGolfCandidate.T3M.Keygen.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
end SigGolfCandidate.T3M.Keygen.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Keygen.PackedBlocks
class Code (im : Image) : Prop where
  entry : CodeAt im (pcOf 1032) expand_entry
  layer0 : CodeAt im (pcOf 1247) expand_layer0
  layer1 : CodeAt im (pcOf 1249) expand_layer1
  layer23 : CodeAt im (pcOf 1251) expand_layer23
  inc : CodeAt im (pcOf 1252) expand_inc
  body : CodeAt im (pcOf 1253) expand_body
  store : CodeAt im (pcOf 1038) expand_store
variable {im : Image} [Code im]
theorem steps_expand_entry (s : MachineState) (hpc : s.pc = pcOf 1032) :
    Steps im s 1 1 (run_expand_entry.res.toState s) := by
  exact symRun_sound run_expand_entry (Code.entry (im := im)) s hpc (by simp [run_expand_entry.res, rv_simp])

theorem steps_expand_layer0 (s : MachineState) (hpc : s.pc = pcOf 1247) :
    Steps im s 2 2 (run_expand_layer0.res.toState s) := by
  exact symRun_sound run_expand_layer0 (Code.layer0 (im := im)) s hpc (by simp [run_expand_layer0.res, rv_simp])

theorem steps_expand_layer1 (s : MachineState) (hpc : s.pc = pcOf 1249) :
    Steps im s 2 2 (run_expand_layer1.res.toState s) := by
  exact symRun_sound run_expand_layer1 (Code.layer1 (im := im)) s hpc (by simp [run_expand_layer1.res, rv_simp])

theorem steps_expand_layer23 (s : MachineState) (hpc : s.pc = pcOf 1251) :
    Steps im s 2 2 (run_expand_layer23.res.toState s) := by
  exact symRun_sound run_expand_layer23 (Code.layer23 (im := im)) s hpc (by simp [run_expand_layer23.res, rv_simp])

theorem steps_expand_inc (s : MachineState) (hpc : s.pc = pcOf 1252) :
    Steps im s 1 1 (run_expand_inc.res.toState s) := by
  exact symRun_sound run_expand_inc (Code.inc (im := im)) s hpc (by simp [run_expand_inc.res, rv_simp])

theorem steps_expand_body (s : MachineState) (hpc : s.pc = pcOf 1253) :
    Steps im s 19 19 (run_expand_body.res.toState s) := by
  exact symRun_sound run_expand_body (Code.body (im := im)) s hpc (by simp [run_expand_body.res, rv_simp])

theorem steps_expand_store (s : MachineState) (hpc : s.pc = pcOf 1038) :
    Steps im s 3 3 (run_expand_store.res.toState s) := by
  exact symRun_sound run_expand_store (Code.store (im := im)) s hpc (by simp [run_expand_store.res, rv_simp])
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
open SigGolfCandidate.T3M.Keygen.PackedBlocks
variable {im : SigGolfCandidate.Legacy.Riscv.Image} [Code im]
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
/-- Pairing stage 1: expand's chain header store ends at 1040 (1041 is `jal 43764`, the G/F step block); `t3`
holds `CHAIN`. -/
structure ExpHeaderPost (s t : MachineState) (height : Nat) : Prop where
  low : t.getMem (BitVec.ofNat 64 (0x201A0 + 16)) = packedAt s height
  high : t.getMem (BitVec.ofNat 64 (0x201A0 + 24)) = routedAt s height >>> 32
  x28 : t.getReg .x28 = BitVec.ofNat 64 0x201A0
  regs : RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30]
  frame : Frame s t (fun A => A = 0x201A0 + 16 ∨ A = 0x201A0 + 24)
theorem expand_header_0 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 0#64) :
    ∃ t, Steps im s 25 25 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 12 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_body.res.toState s1
  have h2 := steps_expand_body (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_store.res.toState s2
  have h3 := steps_expand_store (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s3, (((h0.trans h1).trans h2).trans h3), ?_, ?_⟩
  · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_1 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 1#64) :
    ∃ t, Steps im s 28 28 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 7 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_inc.res.toState s2
  have h3 := steps_expand_inc (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_inc.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_2 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 2#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
theorem expand_header_3 (s : MachineState) (hpc : s.pc = pcOf 1032)
    (h8 : s.getReg .x8 = 3#64) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 1041 ∧ ExpHeaderPost s t 6 := by
  let s0 := run_expand_entry.res.toState s
  have h0 := steps_expand_entry (im := im) s hpc
  let s1 := run_expand_layer0.res.toState s0
  have h1 := steps_expand_layer0 (im := im) s0 (by simp [s0, run_expand_entry.res, rv_simp, h8])
  let s2 := run_expand_layer1.res.toState s1
  have h2 := steps_expand_layer1 (im := im) s1 (by simp [s0, s1, run_expand_entry.res, run_expand_layer0.res, rv_simp, h8])
  let s3 := run_expand_layer23.res.toState s2
  have h3 := steps_expand_layer23 (im := im) s2 (by simp [s0, s1, s2, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, rv_simp, h8])
  let s4 := run_expand_body.res.toState s3
  have h4 := steps_expand_body (im := im) s3 (by simp [s0, s1, s2, s3, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, rv_simp, h8])
  let s5 := run_expand_store.res.toState s4
  have h5 := steps_expand_store (im := im) s4 (by simp [s0, s1, s2, s3, s4, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, rv_simp, h8])
  refine ⟨s5, (((((h0.trans h1).trans h2).trans h3).trans h4).trans h5), ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
  · constructor
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, packedAt, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp, routedAt]
    · simp [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp]
    · intro r hr
      cases r <;> simp_all [s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, s5, s4, s3, s2, s1, s0, run_expand_entry.res, run_expand_layer0.res, run_expand_layer1.res, run_expand_layer23.res, run_expand_body.res, run_expand_store.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
end SigGolfCandidate.T3M.Expand.SharedRecover.PackedBlocks
end
-- ==== merged from T3M_Keygen_Tree ====
section

section



namespace SigGolfCandidate.T3M.RevNet
open SigGolfCandidate.Rv SigGolfCandidate.T3.Rev
theorem tabRev_eq : ∀ n v, Images.tabRev n v = revBits n v
  | 0, _ => rfl
  | n + 1, v => by simp only [Images.tabRev, revBits, tabRev_eq n (v / 2)]
theorem verifyTabWord_eq (j : Nat) : Images.verifyTabWord j = revBits 64 (2048 + j) := tabRev_eq 64 _
def bvA (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .srl x 8#64) (BinOp.eval .sll (BinOp.eval .and x 255#64) 8#64)
def bvS (k M x : BitVec 64) : BitVec 64 :=
  BinOp.eval .or (BinOp.eval .and (BinOp.eval .srl x k) M) (BinOp.eval .sll (BinOp.eval .and x M) k)
def revNetBV (x : BitVec 64) : BitVec 64 :=
  BinOp.eval .sll (bvS 1#64 21845#64 (bvS 2#64 13107#64 (bvS 4#64 3855#64 (bvA x)))) 48#64
@[irreducible] def ok1 (v : Nat) : Bool := revNetBV (BitVec.ofNat 64 v) == BitVec.ofNat 64 (revBits 64 v)
def chk (b : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => ok1 (b + n) && chk b n
theorem ok1_sound {v : Nat} (h : ok1 v = true) : revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  unfold ok1 at h; exact beq_iff_eq.mp h
theorem chk_succ (b n : Nat) : chk b (n + 1) = (ok1 (b + n) && chk b n) := by rw [chk]
theorem chk_sound (b : Nat) : ∀ n, chk b n = true → ∀ v, b ≤ v → v < b + n →
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v)
  | 0, _, v, _, h2 => absurd h2 (by omega)
  | n + 1, h, v, h1, h2 => by
    rw [chk_succ, Bool.and_eq_true] at h
    by_cases hv : v = b + n
    · subst hv; exact ok1_sound h.1
    · exact chk_sound b n h.2 v h1 (by omega)
theorem chk0 : chk 0 1024 = true := by decide +kernel
theorem chk1 : chk 1024 1024 = true := by decide +kernel
theorem chk2 : chk 2048 1024 = true := by decide +kernel
theorem chk3 : chk 3072 1024 = true := by decide +kernel
theorem revNetBV_eq (v : Nat) (hv : v < 2 ^ 12) :
    revNetBV (BitVec.ofNat 64 v) = BitVec.ofNat 64 (revBits 64 v) := by
  rcases (show v < 1024 ∨ (1024 ≤ v ∧ v < 2048) ∨ (2048 ≤ v ∧ v < 3072) ∨ (3072 ≤ v ∧ v < 4096) by omega) with
    h | h | h | h
  · exact chk_sound 0 1024 chk0 v (by omega) (by omega)
  · exact chk_sound 1024 1024 chk1 v h.1 (by omega)
  · exact chk_sound 2048 1024 chk2 v h.1 (by omega)
  · exact chk_sound 3072 1024 chk3 v h.1 (by omega)
end SigGolfCandidate.T3M.RevNet
end

section



section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem sub116_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 116)) (lo : Nat) (hlo : lo < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if lo = 0 then pcOf (b + 159) else pcOf (b + 117)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_116 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_116 h) s hpc (by simp [st_116, blk117_116.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_116, rebase, blk117_116.res, E.eval, CmpOp.eval, h20]
    by_cases h0 : lo = 0
    · subst h0; simp
    · have : BitVec.ofNat 64 lo ≠ 0#64 := fun he => h0 (by
        have := congrArg BitVec.toNat he; rwa [toNat_ofNat_lt hlo] at this)
      simp [h0, this]
  · intro r hr; cases r <;> simp_all [st_116, blk117_116.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_116, blk117_116.res, rv_simp]
theorem sub117_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 117)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 118) ∧ t.getReg .x24 = s.getReg .x20 ∧
      RegsExcept s t [.x24] ∧ Frame s t (fun _ => False) := by
  have hrun := run_117 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_117 h) s hpc (by simp [st_117, blk117_117.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_117, Result.toState_pc, E.eval]
  · simp [st_117, blk117_117.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_117, blk117_117.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_117, blk117_117.res, rv_simp]
theorem sub118_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 118)) (lo k : Nat) (hlo : lo < 2 ^ 40) (hk : k < 2 ^ 40)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 lo) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if k < 2 * lo then pcOf (b + 120) else pcOf (b + 157)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hrun := run_118 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_118 h) s hpc (by simp [st_118, blk117_118.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_118, rebase, blk117_118.res, rv_simp, h20, h24]
    rw [ofNat_shl, show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_slt k (lo * 2 ^ 1) (by omega) (by omega)]
    by_cases hkl : k < 2 * lo
    · simp [hkl, show k < lo * 2 by omega]
    · simp [hkl, show ¬ k < lo * 2 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_118, blk117_118.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_118, blk117_118.res, rv_simp]
theorem slt_shl52n (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) 0#64 = decide (2048 ≤ h0 % 4096) := by
  have e : BitVec.ofNat 64 h0 <<< 52 = BitVec.ofNat 64 (h0 % 4096 * 2 ^ 52) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    norm_num
    omega
  rw [e, BitVec.slt, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have hr := Nat.mod_lt h0 (show 0 < 4096 by norm_num)
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show h0 % 4096 * 2 ^ 52 < 2 ^ 64 by omega)]
  by_cases hc : 2048 ≤ h0 % 4096
  · simp only [hc, decide_true]
    rw [if_neg (by omega)]
    simp <;> omega
  · simp only [hc, decide_false]
    rw [if_pos (by omega)]
    simp <;> omega
theorem slt_shl52n' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< 52) (0 : Word) = decide (2048 ≤ h0 % 4096) := slt_shl52n h0
theorem slt_shl52 (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) (0 : Word) = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
theorem slt_shl52' (h0 : Nat) :
    BitVec.slt (BitVec.ofNat 64 h0 <<< ((52#64 : Word).toNat % 64)) 0#64 = decide (2048 ≤ h0 % 4096) :=
  slt_shl52n h0
/-- Node window (C4, b3cc11b's keygen words): left/right children copied to `NODE`/`NODE + 48`, one-word label
`(x21 ||| tree << 32) + k` at `NODE + 16`, zero high word, `x29 = k % 2` (the half selector). -/
theorem sub120_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat) (ha8 : arena % 8 = 0)
    (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 20 20 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x29 = BitVec.ofNat 64 (k % 2) ∧ t.getReg .x30 = BitVec.ofNat 64 (NODE + 48) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  have hc := codeAt_sub120K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  have hobl : Oblig.all s st_120K.obl := by
    simp only [st_120K, kblk_120.res]
    t3n [h2, h24]
    simp only [NODE] at hdis
    omega
  refine ⟨_, symRun_sound run_120K hc s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, st_120K, kblk_120.res, rv_simp, h24]
    exact ofNat_and1 k
  · simp [st_120K, kblk_120.res, rv_simp]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h9, h24]
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n []
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · simp only [Result.toState_getMem, st_120K, kblk_120.res, NODE]
    t3n [h2, h24]
    congr 2; omega
  · intro r hr; simp at hr; cases r <;> simp_all [st_120K, kblk_120.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, st_120K, kblk_120.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem sub214_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 1004)) (k : Nat) (hk : k < 2 ^ 12) (h24 : s.getReg .x24 = BitVec.ofNat 64 k) :
    ∃ t, Steps image s 28 28 t ∧ t.pc = pcOf (b + 140) ∧
      t.getReg .x7 = BitVec.ofNat 64 (T3.Rev.revBits 64 k) ∧
      RegsExcept s t [.x6, .x7, .x28] ∧ Frame s t (fun _ => False) := by
  have hrun := run_rev h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_rev h) s hpc (by simp [st_rev, blk117_rev.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_rev, Result.toState_pc, E.eval]
  · rw [Result.toState_getReg, ← RevNet.revNetBV_eq k hk, ← h24]
    rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_rev, blk117_rev.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_rev, blk117_rev.res, rv_simp]
theorem valid8_ofNat (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem node48_m24 : BitVec.ofNat 64 (NODE + 48) + BitVec.ofNat 64 18446744073709551592 = BitVec.ofNat 64 (NODE + 24) := by
  rw [ofNat_add_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat, NODE]
theorem sub140_obl (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    Oblig.all s st_140.obl := by
  simp only [st_140, blk117_140.res, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
    BitVec.ofNat_eq_ofNat]
  rw [h30, node48_m24]
  exact valid8_ofNat _ (by simp only [NODE]) (by simp only [NODE]; omega)
theorem sub140_m24 (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) :
    memEval s st_140.mem (BitVec.ofNat 64 (NODE + 24)) = s.getReg .x7 := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
theorem sub140_frame (s : MachineState) (h30 : s.getReg .x30 = BitVec.ofNat 64 (NODE + 48)) (X : Nat)
    (hX : X < 2 ^ 64) (hn : X ≠ 131608) :
    memEval s st_140.mem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
  simp only [st_140, blk117_140.res]
  t3n [h30, NODE]
  rw [if_neg (by omega)]
/-- C4 (b3cc11b's keygen word): the hash call setup also scales the half selector, `x29 = 16 p`. -/
theorem sub140_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 140)) (p : Nat) (h29 : s.getReg .x29 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (p * 2 ^ 4) ∧
      RegsExcept s t [.x10, .x11, .x12, .x29] ∧ Frame s t (fun _ => False) := by
  have hc := codeAt_sub140K h
  obtain ⟨rfl, rfl⟩ := h.2.2.2.2
  refine ⟨_, symRun_sound run_140K hc s hpc (by simp [st_140K, kblk_140.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, E.eval]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp [st_140K, kblk_140.res, rv_simp]
  · simp only [Result.toState_getReg, st_140K, kblk_140.res, rv_simp, h29]
    rw [ofNat_shl]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [st_140K, kblk_140.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_140K, kblk_140.res, rv_simp]
def revX (tag : Nat) : Nat := if tag = 10 then 28 else 0
/-- Base of the node label word in the `s5` register: the C4 top label is the heap itself (base 0; it was 64); the
lower trees (the sign's) keep `hyperWord (lay - 1) tree`. -/
def nodeLo (lay tree : Nat) : Nat := if lay = 0 then 0 else (T3.hyperWord (lay - 1) tree).toNat
theorem nodeLo_mod (lay tree : Nat) : nodeLo lay tree % 4096 < 2048 := by
  unfold nodeLo; split
  · decide
  · rw [T3.hyperWord_toNat]; simp only [Nat.reducePow]; omega
/-- C4: the top node tweak is the one-word label `0#64 ++ heap` (`nodeLo 0 tree = 0`). -/
theorem nodeTweak_3_top (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) :
    T3.nodeTweak 3 0 tree heap = 0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap) := by
  rw [T3.nodeTweak_top, T3.topNodeWord_eq h1 h2]
  simp [nodeLo]
/-- The tree node block from `b + 120` to the hash call (C4: no reversed labels, one-word label). -/
theorem sub120_full {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 120)) (arena k tree h0 : Nat)
    (ha8 : arena % 8 = 0) (hk : 32 * k + 32 + arena ≤ 2 ^ 24) (htree : tree < 2 ^ 32)
    (hdis : NODE + 64 ≤ arena + 32 * k ∨ arena + 32 * k + 32 ≤ NODE)
    (h2 : s.getReg .x2 = BitVec.ofNat 64 arena) (h24 : s.getReg .x24 = BitVec.ofNat 64 k)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h21 : s.getReg .x21 = BitVec.ofNat 64 h0) :
    ∃ t, Steps image s 26 26 t ∧ t.pc = pcOf (b + 146) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧ t.getReg .x29 = BitVec.ofNat 64 (k % 2 * 2 ^ 4) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (arena + 32 * k)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (s.getReg .x21 ||| (BitVec.ofNat 64 tree <<< 32)) + BitVec.ofNat 64 k ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 16)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (arena + 32 * k + 24)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30, .x10, .x11, .x12, .x29] ∧
      Frame s t (fun X => X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨
        X = NODE + 56) := by
  obtain ⟨t1, st1, t1pc, t1x29, t1x30, m0, m8, m16, m24, m48, m56, t1r, t1f⟩ :=
    sub120_spec h s hpc arena k tree h0 ha8 hk htree hdis h2 h24 h9 h21
  obtain ⟨t, stt, tpc, tx10, tx11, tx12, tx29, tr, tf⟩ := sub140_spec h t1 t1pc (k % 2) t1x29
  have g : ∀ X, X < 2 ^ 64 → t.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX => tf.get hX (fun h => h)
  refine ⟨t, (st1.trans stt).of_eq (by omega) (by omega), tpc, tx10, tx11, tx12, tx29, ?_, ?_, ?_, ?_, ?_, ?_,
    t1r.trans tr, (t1f.trans tf).mono (fun X _ hX => by rcases hX with hX | hX; exact hX; exact hX.elim)⟩
  · rw [g NODE (by decide), m0]
  · rw [g (NODE + 8) (by decide), m8]
  · rw [g (NODE + 16) (by decide), m16]
  · rw [g (NODE + 24) (by decide), m24]
  · rw [g (NODE + 48) (by decide), m48]
  · rw [g (NODE + 56) (by decide), m56]
theorem fetch_sub146 {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 146)) : fetch image s = some (.base .ECALL) :=
  ((codeAt_sub_146 h).fetch s hpc).trans rfl
theorem sub159_spec {image : Image} {b : Nat} (h : SubAt image b) (s : MachineState)
    (hpc : s.pc = pcOf (b + 159)) (k : Nat) (h1 : s.getReg .x1 = pcOf k) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf k ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have hrun := run_159 h.2.1
  refine ⟨_, symRun_sound hrun (codeAt_sub_159 h) s hpc (by simp [st_159, blk117_159.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_159, blk117_159.res, rv_simp, h1, pcOf_and_max]
  · intro r hr; cases r <;> simp_all [st_159, blk117_159.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_159, blk117_159.res, rv_simp]
end SigGolfCandidate.T3M.Keygen
end
section
namespace SigGolfCandidate.T3M.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Digest buildLevels buildLevel nodeHash shortHash header pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
structure LevArgs where
  tag : Nat
  lay : Nat
  tree : Nat
  h : Nat
  arena : Nat
  ret : Nat
namespace LevArgs
variable (B : LevArgs)
def levK : Nat := 3 + sumTo (fun j => 6 + (39 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levC : Nat := 3 + sumTo (fun j => 6 + (46 + revX B.tag) * 2 ^ (B.h - 1 - j)) B.h + 2
def levN : Nat := sumTo (fun j => 2 ^ (B.h - 1 - j)) B.h
end LevArgs
def LevW (B : LevArgs) (X : Nat) : Prop :=
  X = NODE ∨ X = NODE + 8 ∨ X = NODE + 16 ∨ X = NODE + 24 ∨ X = NODE + 48 ∨ X = NODE + 56 ∨
    (NOUT ≤ X ∧ X < NOUT + 32) ∨ (B.arena + 16 ≤ X ∧ X < B.arena + 16 * 2 ^ B.h)
def levRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x24, .x28, .x29, .x30]
structure LevPre (s : MachineState) (B : LevArgs) (leaves : List Digest) : Prop where
  x1 : s.getReg .x1 = pcOf B.ret
  x2 : s.getReg .x2 = BitVec.ofNat 64 B.arena
  x5 : s.getReg .x5 = 0
  x9 : s.getReg .x9 = BitVec.ofNat 64 B.tree
  x15 : s.getReg .x15 = BitVec.ofNat 64 B.h
  x21 : s.getReg .x21 = BitVec.ofNat 64 (nodeLo B.lay B.tree)
  tag3 : B.tag = 3
  hlay : B.lay < 4
  htree : B.tree < 2 ^ 32
  hh1 : 1 ≤ B.h
  hh : B.h ≤ 12
  ha8 : B.arena % 8 = 0
  ha : B.arena + 16 * 2 ^ (B.h + 1) ≤ 2 ^ 24
  has : NOUT + 32 ≤ B.arena ∨ B.arena + 16 * 2 ^ (B.h + 1) ≤ NODE
  z32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  z40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  hlen : leaves.length = 2 ^ B.h
  hleaves : DigsAt s (B.arena + 16 * 2 ^ B.h) leaves
def HeapAt (t : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest)) : Prop :=
  levels.length = ℓ + 1 ∧ ∀ l ≤ ℓ, (levels.getD l []).length = 2 ^ (B.h - l) ∧
    DigsAt t (B.arena + 16 * 2 ^ (B.h - l)) (levels.getD l [])
structure LevInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ B.h / 2 ^ (ℓ + 1))
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
structure NodeInv (s0 : MachineState) (B : LevArgs) (ℓ : Nat) (levels : List (List Digest))
    (pre : List Digest) (t : MachineState) : Prop where
  x20 : t.getReg .x20 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1))
  x24 : t.getReg .x24 = BitVec.ofNat 64 (2 ^ (B.h - ℓ - 1) + pre.length)
  regs : RegsExcept s0 t levRegs
  frame : Frame s0 t (LevW B)
  heap : HeapAt t B ℓ levels
  cur : DigsAt t (B.arena + 16 * 2 ^ (B.h - ℓ - 1)) pre
theorem nodeInput_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_nodeInput (tag lay tree heap : Nat) (l r : Digest)
    (hn : T3.packedNodeTag tag := by decide) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header tag lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 tag lay tree tree),
        BitVec.ofNat 64 (T3.nodeWord tag 0 heap), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_packed_header _ _ _ _ _ hn, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
theorem wordsOf_nodeInput_3 (lay tree heap : Nat) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (header 3 lay tree 0 heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (hdr0 3 lay tree tree),
        BitVec.ofNat 64 (hdr1 heap 0), 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_nodeInput 3 lay tree heap l r (by decide), nodeWord_3]
/-- C4: the words of a top node input (label `nodeLo 0 tree + heap`, zero high word, zero pad). -/
theorem wordsOf_nodeInputT (tree heap : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (l r : Digest) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak 3 0 tree heap) ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 (nodeLo 0 tree + heap),
        0, 0, 0, r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16, nodeTweak_3_top tree heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (nodeLo 0 tree + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]; rfl
theorem nodeInputT_length (tag lay tree heap : Nat) (l r : Digest) :
    (bytesLE 16 l ++ bytesLE 16 (T3.nodeTweak tag lay tree heap) ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem two_pow_split {h l : Nat} (hl : l < h) : 2 ^ (h - l) = 2 * 2 ^ (h - l - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega
/-! The keygen top-tree level routine (top-bytes layer: node nonces) is proved in `TopTree.lean`
(`sub113`/`sub147`/`sub157` now hook into KINIT/KCHK/KNEXT). -/
end SigGolfCandidate.T3M.Keygen
end
end
end
-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev ENC : Nat := 0x20260
abbrev NODE : Nat := 0x20200
def hookCode : List (BitVec 32) := [0x5392606f]
sym_block hookCodeBlock := symRun { noAlias := true } hookCode (pcOf 1117) 30
def testCode : List (BitVec 32) := [0x41478e33,0xfffe0e13]
def branch1Code : List (BitVec 32) := [34479715]
def branch2Code : List (BitVec 32) := [33819747]
def pairCode : List (BitVec 32) := [134967,638521107,134839,537824915,963331,9352067,7286819,8336419,51294979,59683715,40843299,41892899,32871]
sym_block pairCodeBlock := symRun { noAlias := true } pairCode (pcOf 40879) 30
def backCode : List (BitVec 32) := [0xa8cd906f]
sym_block backCodeBlock := symRun { noAlias := true } backCode (pcOf 40892) 30
def selectCode : List (BitVec 32) := testCode ++ branch1Code
sym_block selectBlock := symRun { noAlias := true } selectCode (pcOf 40875) 30
sym_block layerBranch := symRun { noAlias := true } branch2Code (pcOf 40878) 30
def remaining (s : MachineState) : Word := s.getReg .x15 - s.getReg .x20 - 1
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
abbrev CHAIN : Nat := 0x201A0
abbrev LEAFPK : Nat := 0x20600
macro "ex_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
theorem ex_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := ofNat_slt a b ha hb
theorem ex_beq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [this, h]
def e_hdrA : List (BitVec 32) := [1050259,29791923,1707539,29974067,29787827,710049903]
sym_block eb_hdrA := symRun { noAlias := true } e_hdrA (pcOf 1119) 30
/-- C4: the top fold label is the heap (`t1 = a3`) with a zero high word (`t2 = 0`). -/
def e_hdrB : List (BitVec 32) := [915,426771,33817187]
sym_block eb_hdrB := symRun { noAlias := true } e_hdrB (pcOf 42765) 30
def e_hdrC : List (BitVec 32) := [17077011,538141459,0xfff40f13,51322643,31679283,0xc100f13,59711251,756023407]
sym_block eb_hdrC := symRun { noAlias := true } e_hdrC (pcOf 42768) 30
def e_hdrD : List (BitVec 32) := [0xd44d706f]
sym_block eb_hdrD := symRun { noAlias := true } e_hdrD (pcOf 42776) 30
def e_hdrE : List (BitVec 32) := [134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
sym_block eb_hdrE := symRun { noAlias := true } e_hdrE (pcOf 1129) 30
def e_hpA : List (BitVec 32) := [0xf49333,19071795,16978707,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,267875]
sym_block eb_hpA := symRun { noAlias := true } e_hpA (pcOf 42741) 30
def e_hpZ : List (BitVec 32) := [929827,930851,0xbb0d706f]
sym_block eb_hpZ := symRun { noAlias := true } e_hpZ (pcOf 42755) 30
def e_hpJ : List (BitVec 32) := [0xbb0d706f]
sym_block eb_hpJ := symRun { noAlias := true } e_hpJ (pcOf 42757) 30
def e_w1009 : List (BitVec 32) := [2451]
sym_block eb_w1009 := symRun { noAlias := true } e_w1009 (pcOf 1009) 30
/-- T51: 42759 (#938 `beq s0,zero,42763`, the top slot `+32` path) is a NOP: the endpad top leaf uses the lower
slots (`end_0` at `LEAFPK`, `end_i` at `LEAFPK + 16 i + 16`). -/
def e_slA : List (BitVec 32) := [4824595,0x13]
sym_block eb_slA := symRun { noAlias := true } e_slA (pcOf 42758) 30
def e_slB : List (BitVec 32) := [624739]
sym_block eb_slB := symRun { noAlias := true } e_slB (pcOf 42760) 30
def e_slN : List (BitVec 32) := [17698323,0xc48d706f]
sym_block eb_slN := symRun { noAlias := true } e_slN (pcOf 42761) 30
def e_slT : List (BitVec 32) := [34475539,0xc40d706f]
sym_block eb_slT := symRun { noAlias := true } e_slT (pcOf 42763) 30
def e_slZ : List (BitVec 32) := [0xc40d706f]
sym_block eb_slZ := symRun { noAlias := true } e_slZ (pcOf 42764) 30
/-! T51 KMAX (54532..54542, from 1158 `j 54532`): `s5` = the top chain cap `maxDigit 0 i` (5 for `i < 27`, 4 for
`i < 48`, 6 for `i < 50`, else 5), then `j 1031`. -/
def e_kmax0 : List (BitVec 32) := [0x00500a93,0x01b00e13,0x03c9c063]
sym_block eb_kmax0 := symRun { noAlias := true } e_kmax0 (pcOf 54532) 30
def e_kmax1 : List (BitVec 32) := [0x00400a93,0x03000e13,0x01c9ca63]
sym_block eb_kmax1 := symRun { noAlias := true } e_kmax1 (pcOf 54535) 30
def e_kmax2 : List (BitVec 32) := [0x00600a93,0x03200e13,0x01c9c463]
sym_block eb_kmax2 := symRun { noAlias := true } e_kmax2 (pcOf 54538) 30
def e_kmax3 : List (BitVec 32) := [0x00500a93,0xbe5cb06f]
sym_block eb_kmax3 := symRun { noAlias := true } e_kmax3 (pcOf 54541) 30
def e_kmax4 : List (BitVec 32) := [0xbe5cb06f]
sym_block eb_kmax4 := symRun { noAlias := true } e_kmax4 (pcOf 54542) 30
/-! T51 GT (54543..54552, from 49311 `j 54543`): `t1` = the G terminal step `maxDigit 0 i - 1` (4, 3 for
`27 <= i < 48`, 5 for `i = 48`) and 7 for chain 0 (it keeps the HIGH half on every step), then `j 49315`. -/
def e_gt0 : List (BitVec 32) := [0x00400313,0xfe598393,0x0153b393,0x40730333,0xfd098393,0x0013b393,0x00730333,
  0x00099463]
sym_block eb_gt0 := symRun { noAlias := true } e_gt0 (pcOf 54543) 30
def e_gt1 : List (BitVec 32) := [0x00700313,0xe2dfa06f]
sym_block eb_gt1 := symRun { noAlias := true } e_gt1 (pcOf 54551) 30
def e_gt2 : List (BitVec 32) := [0xe2dfa06f]
sym_block eb_gt2 := symRun { noAlias := true } e_gt2 (pcOf 54552) 30
/-! C2 + C3 (FULL) trampolines: chain tail at 43451 (from 1047), left-child current value at 43462 (from 1103),
packed lower node word at 43467 (from 42775). -/
def e_hdrT : List (BitVec 32) := [31679283,13828915,1475543827,915,2795331695]
sym_block eb_hdrT := symRun { noAlias := true } e_hdrT (pcOf 43467) 30
def e_ct0 : List (BitVec 32) := [34181731]
sym_block eb_ct0 := symRun { noAlias := true } e_ct0 (pcOf 43451) 30
def e_ct1 : List (BitVec 32) := [33816675]
sym_block eb_ct1 := symRun { noAlias := true } e_ct1 (pcOf 43452) 30
def e_ct2 : List (BitVec 32) := [6292243,6954083]
sym_block eb_ct2 := symRun { noAlias := true } e_ct2 (pcOf 43453) 30
def e_ct3 : List (BitVec 32) := [134711,504247043,512635779,476985379,478034979,1706515,2426232943]
sym_block eb_ct3 := symRun { noAlias := true } e_ct3 (pcOf 43455) 30
def e_ct4 : List (BitVec 32) := [1706515,2426232943]
sym_block eb_ct4 := symRun { noAlias := true } e_ct4 (pcOf 43460) 30
/-- C4: the top layer's left child also reads the high half (the `beq s0` skip is a NOP). -/
def e_lcA : List (BitVec 32) := [134839,604933779,19]
sym_block eb_lcA := symRun { noAlias := true } e_lcA (pcOf 43462) 30
def e_lcB : List (BitVec 32) := [17731219,2715639919]
sym_block eb_lcB := symRun { noAlias := true } e_lcB (pcOf 43465) 30
def e_lcC : List (BitVec 32) := [2715639919]
def e_lcD : List (BitVec 32) := [134967,537857811,963331,9352067,7286819,8336419,134967,588189459,733955,9122691,7286819,8336419]
sym_block eb_lcD := symRun { noAlias := true } e_lcD (pcOf 1105) 30
/-- C3 (FULL): extra steps of the chain tail trampoline over the old `addi s4; jal` (2 steps). -/
def trXE (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5
theorem trXE_le (lay i m : Nat) : trXE lay i m ≤ 10 := by unfold trXE; split_ifs <;> omega
/-- C2 (FULL) + C4: offset of the current value (a left child) in the node output: every layer reads the high half. -/
def hiOff (_lay : Nat) : Nat := 16
def slotOff (_lay : T3.Layer) (c : Nat) : Nat := if c = 0 then 0 else 16 * c + 16
def hpK (lay : T3.Layer) : Nat := if lay = 0 then 19 else 17
def slK (_lay : T3.Layer) (i : Nat) : Nat := if i = 0 then 5 else 6
def hdrK (lay : Nat) : Nat := if lay = 0 then 19 else 31
section blocks
variable (s : MachineState)
theorem lbu_word1027 : decodeInstruction (0x000e4a03 : BitVec 32) = some (.base (.LBU .x20 .x28 0)) := rfl
theorem eb_ct3_regs (t : MachineState) : RegsExcept t (eb_ct3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [eb_ct3.res, rv_simp] <;> rfl
theorem ex_ne (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
  fun he => h ((ofNat_inj hx hy).mp he)
theorem ex_valid (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem eb_hdrT_regs (t : MachineState) : RegsExcept t (eb_hdrT.res.toState t) [.x6, .x7] := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  cases r <;> simp_all [eb_hdrT.res, rv_simp] <;> rfl
theorem eb_hdrT_frame (t : MachineState) : Frame t (eb_hdrT.res.toState t) (fun _ => False) := by
  intro A _ _; simp [eb_hdrT.res, rv_simp]
theorem eb_hdrT_x6 (t : MachineState) :
    (eb_hdrT.res.toState t).getReg .x6 = (t.getReg .x6 ||| t.getReg .x30) + t.getReg .x13 + BitVec.ofNat 64 1407 := by
  simp only [Result.toState_getReg, eb_hdrT.res, rv_simp]
theorem eb_hdrT_x7 (t : MachineState) : (eb_hdrT.res.toState t).getReg .x7 = 0 := by
  simp only [Result.toState_getReg, eb_hdrT.res, rv_simp]
theorem eb_hdrE_regs (t : MachineState) : RegsExcept t (eb_hdrE.res.toState t) [.x10, .x11, .x12, .x28] := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  cases r <;> simp_all [eb_hdrE.res, rv_simp] <;> rfl
theorem eb_hdrT_pc (t : MachineState) : (eb_hdrT.res.toState t).pc = pcOf 1129 := by
  simp [Result.toState_pc, eb_hdrT.res, E.eval]
/-- the node tweak words written at `NODE + 16` / `NODE + 24`: `WCT9.merkleTweak` (C2 packed word for lower layers). -/
theorem merkleTweak_words_top (tree heap : Nat) (h1 : 1 ≤ heap) (hh : heap < 4096) :
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 0 64 = BitVec.ofNat 64 heap ∧
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 64 64 = 0 := by
  rw [ClaudeWCT.WCT9.merkleTweak_top_low, ClaudeWCT.WCT9.merkleTweak_top_high, T3.topNodeWord_eq h1 hh]
  exact ⟨rfl, rfl⟩
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
class Code (im : Image) : Prop where
  hookCode_at : CodeAt im (pcOf 1117) hookCode
  testCode_at : CodeAt im (pcOf 40875) testCode
  branch1Code_at : CodeAt im (pcOf 40877) branch1Code
  branch2Code_at : CodeAt im (pcOf 40878) branch2Code
  pairCode_at : CodeAt im (pcOf 40879) pairCode
  backCode_at : CodeAt im (pcOf 40892) backCode
  selectCode_at : CodeAt im (pcOf 40875) selectCode
variable {im : Image} [Code im]
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 40879) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairCodeBlock.res.st.obl := by
    simp [pairCodeBlock.res, rv_simp]
  refine ⟨_, symRun_sound pairCodeBlock (Code.pairCode_at (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairCodeBlock.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pairCodeBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairCodeBlock.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem select_spec (s : MachineState) (hpc : s.pc = pcOf 40875) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if remaining s = 0 then pcOf 40878 else pcOf 40892) ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound selectBlock (Code.selectCode_at (im := im)) s hpc (by simp [selectBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · simp [Result.toState_getReg, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · intro r hr; simp at hr; cases r <;> simp_all [selectBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, selectBlock.res, rv_simp]

theorem layer_spec (s : MachineState) (hpc : s.pc = pcOf 40878) :
    ∃ t, Steps im s 1 1 t ∧
      t.pc = (if s.getReg .x8 = 0 then pcOf 40892 else pcOf 40879) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound layerBranch (Code.branch2Code_at (im := im)) s hpc (by simp [layerBranch.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, layerBranch.res, rv_simp]
  · intro r hr; cases r <;> simp [layerBranch.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, layerBranch.res, rv_simp]

theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1117) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 40875 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hookCodeBlock (Code.hookCode_at (im := im)) s hpc (by simp [hookCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, hookCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [hookCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, hookCodeBlock.res, rv_simp]

theorem back_spec (s : MachineState) (hpc : s.pc = pcOf 40892) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1119 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound backCodeBlock (Code.backCode_at (im := im)) s hpc (by simp [backCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, backCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [backCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, backCodeBlock.res, rv_simp]

theorem continue_spec (s : MachineState) (hpc : s.pc = pcOf 1117)
    (hc : remaining s ≠ 0 ∨ s.getReg .x8 = 0) :
    ∃ t k, Steps im s k k t ∧ k ≤ 6 ∧ t.pc = pcOf 1119 ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = remaining s := by
    unfold remaining
    rw [ur.get (by simp), ur.get (by simp)]
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [he] at vp v28
  by_cases hz : remaining s = 0
  · rw [if_pos hz] at vp
    have h8 : v.getReg .x8 = 0 := by
      rw [vr.get (by simp), ur.get (by simp)]
      exact hc.resolve_left (not_not_intro hz)
    obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
    rw [if_pos h8] at wp
    obtain ⟨t, wt, tp, tr, tf⟩ := back_spec (im := im) w wp
    refine ⟨t, 6, ((su.trans uv).trans vw).trans wt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), wr.get (by simp), v28]
    · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
    · exact (((uf.trans vf).trans wf).trans tf).mono (by intro A hA h; simpa using h)
  · rw [if_neg hz] at vp
    obtain ⟨t, vt, tp, tr, tf⟩ := back_spec (im := im) v vp
    refine ⟨t, 5, (su.trans uv).trans vt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), v28]
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)

theorem finish_spec (s : MachineState) (hpc : s.pc = pcOf 1117) (ret : Nat)
    (hz : remaining s = 0) (hl : s.getReg .x8 ≠ 0) (hra : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = 0 := by unfold remaining; rw [ur.get (by simp), ur.get (by simp)]; exact hz
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [if_pos he] at vp
  have h8 : v.getReg .x8 ≠ 0 := by rw [vr.get (by simp), ur.get (by simp)]; exact hl
  obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
  rw [if_neg h8] at wp
  obtain ⟨t, wt, tp, m0, m8, m48, m56, tr, tf⟩ := pair_spec (im := im) w wp ret
    (by rw [wr.get (by simp), vr.get (by simp), ur.get (by simp)]; exact hra)
  have fsw : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by intro A hA h; simpa using h)
  refine ⟨t, ((su.trans uv).trans vw).trans wt, tp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, fsw.get (by decide) (by simp)]
  · rw [m8, fsw.get (by decide) (by simp)]
  · rw [m48, fsw.get (by decide) (by simp)]
  · rw [m56, fsw.get (by decide) (by simp)]
  · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
  · exact (fsw.trans tf).mono (by intro A hA h; simpa using h)

end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
def seg_n1139 : List (BitVec 32) := [0x1202906f]
def seg_1140 : List (BitVec 32) := [4228647955,1706515,4020236399]
def nonce_A : List (BitVec 32) := [0xc00e13,0xdc79863]
def nonce_B : List (BitVec 32) := [0xb00e13,0xdca7463]
/-- T51: 43199 `addi a3,s4,1` (`h`), 43200 `j 54553` (ZB; #938 `mv a4,a3`, then 43201..43214 computed `b = h`). -/
def nonce_C : List (BitVec 32) := [0x1a0693,0x1640b06f]
/-! T51 ZB (54553..54568): `a4 = b_h = topZeroBits h` (0 for `h < 3`, 1 for `h = 3`, else `h - 3`) and the zero-test
mask `t6` (0 for `b_h = 0`, the top `b_h` bits, bits 40..47 for `h = 11`), then `j 43215`. -/
def nonce_Z0 : List (BitVec 32) := [0x00000713,0x00000f93,0x00300e13,0x03c6c863]
def nonce_Z1 : List (BitVec 32) := [0xffd68713,0x00071463]
def nonce_Z2 : List (BitVec 32) := [0x00100713,0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z3 : List (BitVec 32) := [0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z4 : List (BitVec 32) := [0x0ff00f93,0x028f9f93,0xe9df406f]
def nonce_Z5 : List (BitVec 32) := [0xe9df406f]
def nonce_D : List (BitVec 32) := [0x800e13,0x80006f]
def nonce_E : List (BitVec 32) := [0x4000e13,0x40ee0e33,0xfff00f93,0x1cf9fb3,0xb00e13,0x1c69663]
def nonce_F : List (BitVec 32) := [0x7ff00f93,0x22f9f93]
def nonce_G : List (BitVec 32) := [0x6800893,0xe898b3,0xd95eb3,0x1efe93,0x100f13,0x41df0eb3,0x4e9e93,0x20f37,0x240f0f13,0x1ee8eb3]
def nonce_L : List (BitVec 32) := [0x8ebf03,0x1ff7f33,0x20f0a63]
def nonce_H : List (BitVec 32) := [0x20e37,0x220e3f03,0x1f0f13,0x31f7263]
def nonce_I : List (BitVec 32) := [0x23ee3023,0x20537,0x20050513,0x4000593,0x20637,0x24060613]
def nonce_E43238 : List (BitVec 32) := [0x73]
def nonce_J : List (BitVec 32) := [0xfc9ff06f]
def nonce_K : List (BitVec 32) := [0x20e37,0x220e3f03,0x220e3023,0x66e37,0x752e3c23,0x3a1e93,0x1de0e33,0x71ee3023]
def nonce_S : List (BitVec 32) := [0x10b0b13,0xe0dd606f]
def expHdrK (lay : T3.Layer) : Nat := if lay.val = 0 then 25 else if lay.val = 1 then 28 else 29
theorem expHdrK_le (lay : T3.Layer) : expHdrK lay ≤ 29 := by unfold expHdrK; split_ifs <;> omega
class Code (im : Image) : Prop where
  e_hdrA_at : CodeAt im (pcOf 1119) e_hdrA
  e_hdrB_at : CodeAt im (pcOf 42765) e_hdrB
  e_hdrC_at : CodeAt im (pcOf 42768) e_hdrC
  e_hdrD_at : CodeAt im (pcOf 42776) e_hdrD
  e_hdrE_at : CodeAt im (pcOf 1129) e_hdrE
  e_hpA_at : CodeAt im (pcOf 42741) e_hpA
  e_hpZ_at : CodeAt im (pcOf 42755) e_hpZ
  e_hpJ_at : CodeAt im (pcOf 42757) e_hpJ
  e_w1009_at : CodeAt im (pcOf 1009) e_w1009
  e_slA_at : CodeAt im (pcOf 42758) e_slA
  e_slB_at : CodeAt im (pcOf 42760) e_slB
  e_slN_at : CodeAt im (pcOf 42761) e_slN
  e_slZ_at : CodeAt im (pcOf 42764) e_slZ
  codeAt_1010 : CodeAt im (pcOf 1010) seg_1010
  codeAt_1011 : CodeAt im (pcOf 1011) seg_1011
  codeAt_1027 : CodeAt im (pcOf 1027) seg_1027
  codeAt_1028 : CodeAt im (pcOf 1028) seg_1028
  codeAt_1030 : CodeAt im (pcOf 1030) seg_1030
  codeAt_1031 : CodeAt im (pcOf 1031) seg_1031
  -- Witness stack: 1041 `jal 49300` and the chain step block 49300..49337.
  codeAt_1041 : CodeAt im (pcOf 1041) seg_1041
  codeAt_49300 : CodeAt im (pcOf 49300) seg_49300
  codeAt_49301 : CodeAt im (pcOf 49301) seg_49301
  codeAt_49303 : CodeAt im (pcOf 49303) seg_49303
  codeAt_49306 : CodeAt im (pcOf 49306) seg_49306
  codeAt_49309 : CodeAt im (pcOf 49309) seg_49309
  codeAt_49311 : CodeAt im (pcOf 49311) seg_49311
  e_gt0_at : CodeAt im (pcOf 54543) e_gt0
  e_gt1_at : CodeAt im (pcOf 54551) e_gt1
  e_gt2_at : CodeAt im (pcOf 54552) e_gt2
  codeAt_49315 : CodeAt im (pcOf 49315) seg_49315
  codeAt_49316 : CodeAt im (pcOf 49316) seg_49316
  codeAt_49327 : CodeAt im (pcOf 49327) seg_49327
  codeAt_49328 : CodeAt im (pcOf 49328) seg_49328
  codeAt_49329 : CodeAt im (pcOf 49329) seg_49329
  codeAt_49331 : CodeAt im (pcOf 49331) seg_49331
  codeAt_49336 : CodeAt im (pcOf 49336) seg_49336
  codeAt_49337 : CodeAt im (pcOf 49337) seg_49337
  codeAt_1049 : CodeAt im (pcOf 1049) seg_1049
  codeAt_1052 : CodeAt im (pcOf 1052) seg_1052
  codeAt_1063 : CodeAt im (pcOf 1063) seg_1063
  codeAt_1072 : CodeAt im (pcOf 1072) seg_1072
  codeAt_1073 : CodeAt im (pcOf 1073) seg_1073
  codeAt_1076 : CodeAt im (pcOf 1076) seg_1076
  codeAt_1077 : CodeAt im (pcOf 1077) seg_1077
  codeAt_1080 : CodeAt im (pcOf 1080) seg_1080
  codeAt_1099 : CodeAt im (pcOf 1099) seg_1099
  codeAt_1138 : CodeAt im (pcOf 1138) seg_1138
  codeAt_1139 : CodeAt im (pcOf 1139) seg_n1139
  codeAt_1140 : CodeAt im (pcOf 1140) seg_1140
  codeAt_nA : CodeAt im (pcOf 43195) nonce_A
  codeAt_nB : CodeAt im (pcOf 43197) nonce_B
  codeAt_nC : CodeAt im (pcOf 43199) nonce_C
  codeAt_nZ0 : CodeAt im (pcOf 54553) nonce_Z0
  codeAt_nZ1 : CodeAt im (pcOf 54557) nonce_Z1
  codeAt_nZ2 : CodeAt im (pcOf 54559) nonce_Z2
  codeAt_nZ3 : CodeAt im (pcOf 54560) nonce_Z3
  codeAt_nZ4 : CodeAt im (pcOf 54566) nonce_Z4
  codeAt_nZ5 : CodeAt im (pcOf 54568) nonce_Z5
  codeAt_nG : CodeAt im (pcOf 43215) nonce_G
  codeAt_nL : CodeAt im (pcOf 43225) nonce_L
  codeAt_nH : CodeAt im (pcOf 43228) nonce_H
  codeAt_nI : CodeAt im (pcOf 43232) nonce_I
  codeAt_n43238 : CodeAt im (pcOf 43238) nonce_E43238
  codeAt_nJ : CodeAt im (pcOf 43239) nonce_J
  codeAt_nK : CodeAt im (pcOf 43240) nonce_K
  codeAt_nS : CodeAt im (pcOf 43248) nonce_S
  codeAt_1143 : CodeAt im (pcOf 1143) seg_1143
  codeAt_1158 : CodeAt im (pcOf 1158) seg_1158
  e_kmax0_at : CodeAt im (pcOf 54532) e_kmax0
  e_kmax1_at : CodeAt im (pcOf 54535) e_kmax1
  e_kmax2_at : CodeAt im (pcOf 54538) e_kmax2
  e_kmax3_at : CodeAt im (pcOf 54541) e_kmax3
  e_kmax4_at : CodeAt im (pcOf 54542) e_kmax4
  codeAt_997 : CodeAt im (pcOf 997) seg_997
  -- Stage 2 (C2 + C3, #866): the chain tail trampoline (from 1047), the left-child current value trampoline
  -- (from 1103) and the packed lower node word (from 42775); the same words at the same addresses as `image`.
  e_hdrT_at : CodeAt im (pcOf 43467) e_hdrT
  e_ct0_at : CodeAt im (pcOf 43451) e_ct0
  e_ct1_at : CodeAt im (pcOf 43452) e_ct1
  e_ct2_at : CodeAt im (pcOf 43453) e_ct2
  e_ct3_at : CodeAt im (pcOf 43455) e_ct3
  e_ct4_at : CodeAt im (pcOf 43460) e_ct4
  e_lcA_at : CodeAt im (pcOf 43462) e_lcA
  e_lcB_at : CodeAt im (pcOf 43465) e_lcB
  e_lcC_at : CodeAt im (pcOf 43466) e_lcC
  e_lcD_at : CodeAt im (pcOf 1105) e_lcD
variable {im : Image} [Code im]
variable [BCBlocks.Code im] [PackedBlocks.Code im]
variable (s : MachineState)
theorem rl997_spec (hpc : s.pc = pcOf 997) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps im s (hpK lay) (hpK lay) t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42741 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_997 (Code.codeAt_997 (im := im)) s hpc (by simp [eblk_997.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_997.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  have g15 : t1.getReg .x15 = BitVec.ofNat 64 (T3.height lay) := by rw [r1.get (by decide), h15]
  obtain ⟨t2, s2, p2, m16, m24, x28, r2, f2⟩ : ∃ t, Steps im t1 14 14 t ∧
      t.pc = (if lay = 0 then pcOf 42755 else pcOf 42757) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧ t.getReg .x28 = BitVec.ofNat 64 LEAFPK ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, symRun_sound eb_hpA (Code.e_hpA_at (im := im)) t1 p1
      (by simp [eb_hpA.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hpA.res, E.eval, CmpOp.eval, g8, bne]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay.val 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0
      · subst h0; simp
      · have : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp [h0, this]
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [g8, g9, g18, g15, LEAFPK]
      have hh : T3.height lay < 64 := by fin_cases lay <;> decide
      rw [Nat.mod_eq_of_lt (by omega : T3.height lay < 18446744073709551616), Nat.mod_eq_of_lt hh,
        show (513#64) = BitVec.ofNat 64 513 from rfl,
        ofNat_or_disjoint 513 ((tree * 2 ^ T3.height lay + leaf) * 65536) 16 (by decide) (by omega),
        ofNat_or_disjoint' _ (↑lay * 281474976710656) 48 (by omega) (by omega),
        show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
        ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
      unfold T3.hyperWord
      congr 1
      rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : lay.val < 256)]
      omega
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [LEAFPK]
    · simp [eb_hpA.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_hpA.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, eb_hpA.res]
      t3n []
      simp only [LEAFPK] at hn
      rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨t3, s3, p3, z0, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 3 else 1) (if lay = 0 then 3 else 1) t ∧
      t.pc = pcOf 1009 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept t2 t [] ∧ Frame t2 t (fun A => A = LEAFPK ∨ A = LEAFPK + 8) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      refine ⟨_, (symRun_sound eb_hpZ (Code.e_hpZ_at (im := im)) t2 p2
        (by simp [eb_hpZ.res, rv_simp, x28, accessValid_iff, MEMORY_BYTES, LEAFPK])).of_eq (by simp [h0, eb_hpZ.res])
        (by simp [h0, eb_hpZ.res]),
        ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpZ.res, E.eval]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · intro r hr; cases r <;> rfl
      · intro A hA hn
        simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28]
        simp only [LEAFPK] at hn ⊢
        rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg h0] at p2
      refine ⟨_, (symRun_sound eb_hpJ (Code.e_hpJ_at (im := im)) t2 p2 (by simp [eb_hpJ.res, rv_simp])).of_eq (by simp [h0, eb_hpJ.res])
        (by simp [h0, eb_hpJ.res]), ?_, fun h => absurd h h0, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpJ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
  obtain ⟨t4, s4, p4, x19, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1010 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t3 t [.x19] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_w1009 (Code.e_w1009_at (im := im)) t3 p3 (by simp [eb_w1009.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_w1009.res, E.eval]
    · simp [eb_w1009.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_w1009.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_w1009.res, rv_simp]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hpK; split_ifs <;> simp_all)
    (by unfold hpK; split_ifs <;> simp_all), p4, x19, ?_, ?_, fun h => ?_,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h <;> simp only [LEAFPK] at h ⊢ <;> omega)⟩
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m16]
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m24]
  · obtain ⟨a, b⟩ := z0 h
    exact ⟨by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), a],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), b]⟩

theorem rl1010_spec (hpc : s.pc = pcOf 1010) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if n ≤ i then pcOf 1063 else pcOf 1011) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1010 (Code.codeAt_1010 (im := im)) s hpc (by simp [eblk_1010.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1010.res, E.eval, CmpOp.eval, h19, h26]
    rw [ex_slt i n hi hn]
    by_cases hc : n ≤ i
    · simp [hc, show ¬ i < n by omega]
    · simp [hc, show i < n by omega]
  · ex_regs eblk_1010.res
  · intro A _ _; simp [eblk_1010.res, rv_simp]

theorem rl1011_spec (hpc : s.pc = pcOf 1011) (i P W : Nat) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616)
    (hP8 : P % 8 = 0) (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h16 : s.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 W) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf 1027 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getMem (BitVec.ofNat 64 (W + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (W + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ t.getReg .x28 = BitVec.ofNat 64 (i + DIGITS) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) := by
  have ea : ∀ k, BitVec.ofNat 64 i <<< ((4#64 : Word).toNat % 64) + BitVec.ofNat 64 P + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (P + 16 * i + k) := fun k => by
    rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; ring
  have hne : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
    fun x y hx hy h he => h ((ofNat_inj hx hy).mp he)
  have hv : ∀ x : Nat, x % 8 = 0 → x + 8 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 8 = true := fun x h1 h2 => by
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  refine ⟨_, symRun_sound eblk_1011 (Code.codeAt_1011 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1011.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h19, h16, h23,
      ea, ofNat_add_ofNat, show (56#64 : Word) = BitVec.ofNat 64 56 from rfl,
      show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, show (131536#64 : Word) = BitVec.ofNat 64 131536 from rfl,
      show (131544#64 : Word) = BitVec.ofNat 64 131544 from rfl]
    refine ⟨hv _ (by omega) (by omega), hv _ (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hv _ (by omega) (by omega), hv _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_1011.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eblk_1011.res, CHAIN]
      t3n [h19, h16, h23]
      (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h23]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (show W < 2 ^ 64 by omega), toNat_ofNat_lt (show W - 64 < 2 ^ 64 by omega)]
    rw [show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_1011.res
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, eblk_1011.res, rv_simp, h23, ofNat_add_ofNat]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem rl1027_spec (hpc : s.pc = pcOf 1027) (i d : Nat) (hi : i < 64) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (i + DIGITS))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1028 ∧ t.getReg .x20 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have ea : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (DIGITS + i) := by
    rw [h28, show signExtend12 (0 : BitVec 12) = 0 from rfl, add_zero, Nat.add_comm]
  have hv : accessValid (s.getReg .x28 + signExtend12 0) 1 = true := by
    rw [ea, accessValid_iff, toNat_ofNat_lt (by simp only [DIGITS]; omega)]; simp only [MEMORY_BYTES, DIGITS]; omega
  refine ⟨_, steps_lbu (Code.codeAt_1027 (im := im)) hpc lbu_word1027 hv, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = _; rw [hpc, pcOf_add4]
  · have e2 : ∀ (u : MachineState) (v pc : Word), ((u.setReg .x20 v).setPC pc).getReg .x20 = v :=
      fun u v pc => rfl
    rw [e2, ea, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show ((s.setReg .x20 _).setPC _).getReg r = _
    cases r <;> simp_all [MachineState.getReg, MachineState.setReg, MachineState.setPC]
  · intro A _ _; rfl

theorem rl1028_spec (hpc : s.pc = pcOf 1028) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1030 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt hlay] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound eblk_1028 (Code.codeAt_1028 (im := im)) s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h8, hz]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]

theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1158 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 (Code.codeAt_1030 (im := im)) s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]

/-- T51 KMAX steps from 1158 to 1031 (1158 `j 54532`, the cap ladder, `j 1031`). -/
def kmaxSteps (i : Nat) : Nat := if i < 27 then 5 else if i < 48 then 8 else if i < 50 then 11 else 12
theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (kmaxSteps i) (kmaxSteps i) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x21 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i) ∧ RegsExcept s t [.x21, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54532 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1158 (Code.codeAt_1158 (im := im)) s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1158.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  have j4 : ∀ u : MachineState, u.pc = pcOf 54542 → ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf 1031 ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := fun u hu => by
    refine ⟨_, symRun_sound eb_kmax4 (Code.e_kmax4_at (im := im)) u hu (by simp [eb_kmax4.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax4.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have hmd : SigGolfCandidate.T3.maxDigit 0 i =
      (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) := by
    simp [SigGolfCandidate.T3.maxDigit]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 3 3 t ∧
      t.pc = (if i < 27 then pcOf 54542 else pcOf 54535) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t0 t [.x21, .x28] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax0 (Code.e_kmax0_at (im := im)) t0 p0 (by simp [eb_kmax0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax0.res, E.eval, CmpOp.eval, RegFile.get, g19]
      rw [show (27#64 : Word) = BitVec.ofNat 64 27 from rfl, ex_slt i 27 hi (by norm_num)]
      by_cases hi' : i < 27 <;> simp [hi']
    · simp [eb_kmax0.res, rv_simp]
    · ex_regs eb_kmax0.res
    · intro A _ _; simp [eb_kmax0.res, rv_simp]
  by_cases h27 : i < 27
  · rw [if_pos h27] at p1
    obtain ⟨t2, s2, p2, r2, f2⟩ := j4 t1 p1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p2, by rw [r2.get (by decide), x1, hmd, if_pos h27],
      ((r0.trans r1).trans r2).mono (by decide), ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h27] at p1
  have g19a : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), g19]
  obtain ⟨t2, s2, p2, x2, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if i < 48 then pcOf 54542 else pcOf 54538) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept t1 t [.x21, .x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax1 (Code.e_kmax1_at (im := im)) t1 p1 (by simp [eb_kmax1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax1.res, E.eval, CmpOp.eval, RegFile.get, g19a]
      rw [show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, ex_slt i 48 hi (by norm_num)]
      by_cases hi' : i < 48 <;> simp [hi']
    · simp [eb_kmax1.res, rv_simp]
    · ex_regs eb_kmax1.res
    · intro A _ _; simp [eb_kmax1.res, rv_simp]
  by_cases h48 : i < 48
  · rw [if_pos h48] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := j4 t2 p2
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p3, by rw [r3.get (by decide), x2, hmd, if_neg h27, if_pos h48],
      (((r0.trans r1).trans r2).trans r3).mono (by decide),
      (((f0.trans f1).trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h48] at p2
  have g19b : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19a]
  obtain ⟨t3, s3, p3, x3, r3, f3⟩ : ∃ t, Steps im t2 3 3 t ∧
      t.pc = (if i < 50 then pcOf 54542 else pcOf 54541) ∧ t.getReg .x21 = BitVec.ofNat 64 6 ∧
      RegsExcept t2 t [.x21, .x28] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax2 (Code.e_kmax2_at (im := im)) t2 p2 (by simp [eb_kmax2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax2.res, E.eval, CmpOp.eval, RegFile.get, g19b]
      rw [show (50#64 : Word) = BitVec.ofNat 64 50 from rfl, ex_slt i 50 hi (by norm_num)]
      by_cases hi' : i < 50 <;> simp [hi']
    · simp [eb_kmax2.res, rv_simp]
    · ex_regs eb_kmax2.res
    · intro A _ _; simp [eb_kmax2.res, rv_simp]
  by_cases h50 : i < 50
  · rw [if_pos h50] at p3
    obtain ⟨t4, s4, p4, r4, f4⟩ := j4 t3 p3
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p4,
      by rw [r4.get (by decide), x3, hmd, if_neg h27, if_neg h48, if_pos h50],
      ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
      ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h50] at p3
  obtain ⟨t4, s4, p4, x4, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t3 t [.x21] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax3 (Code.e_kmax3_at (im := im)) t3 p3 (by simp [eb_kmax3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax3.res, E.eval]
    · simp [eb_kmax3.res, rv_simp]
    · ex_regs eb_kmax3.res
    · intro A _ _; simp [eb_kmax3.res, rv_simp]
  refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
    (by unfold kmaxSteps; split_ifs <;> omega), p4,
    by rw [x4, hmd, if_neg h27, if_neg h48, if_neg h50],
    ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
    ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1031_spec (hpc : s.pc = pcOf 1031) (st e : Nat) (hs : st < 2 ^ 63) (he : e < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if e ≤ st then pcOf 1049 else pcOf 1032) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1031 (Code.codeAt_1031 (im := im)) s hpc (by simp [eblk_1031.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1031.res, E.eval, CmpOp.eval, h20, h21]
    rw [ex_slt st e hs he]
    by_cases hc : e ≤ st
    · simp [hc, show ¬ st < e by omega]
    · simp [hc, show st < e by omega]
  · ex_regs eblk_1031.res
  · intro A _ _; simp [eblk_1031.res, rv_simp]

theorem rl1032_spec (hpc : s.pc = pcOf 1032) (lay : T3.Layer) (tree leaf i st : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay)
    (hi : i < 64) (hs : st < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧ t.pc = pcOf 1041 ∧
      t.getReg .x28 = BitVec.ofNat 64 CHAIN ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (T3.chainHeader lay tree leaf i st).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := by
  have run : ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧
      t.pc = pcOf 1041 ∧ PackedBlocks.ExpHeaderPost s t (T3.height lay) := by
    fin_cases lay
    · exact PackedBlocks.expand_header_0 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_1 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_2 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_3 (im := im) s hpc h8
  obtain ⟨t, steps, pc, post⟩ := run
  refine ⟨t, steps, pc, post.x28,
    post.low.trans (Keygen.PackedBlocks.packedAt_source s lay tree leaf i st hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (Keygen.PackedBlocks.routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi hs).symm

/-- The F path's C3 tail `jal 43451` (at 49337) and its trampoline (an F chain: `isG = false`). -/
theorem rl1047_spec (hpc : s.pc = pcOf 49337) (lay : T3.Layer) (i m : Nat) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (hG : ClaudeWCT.WCT9.isG lay i = false)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : T3.Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps im s (2 + trXE lay.val i m) (2 + trXE lay.val i m) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      DigAt t (CHAIN + 48) (if ClaudeWCT.WCT9.chainHigh lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hlay : lay.val < 2 ^ 64 := by have := lay.isLt; omega
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43451 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_49337 (Code.codeAt_49337 (im := im)) s hpc (by simp [eblk_49337.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_49337.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have last : ∀ u : MachineState, u.pc = pcOf 43460 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps im u 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound eb_ct4 (Code.e_ct4_at (im := im)) u hu (by simp [eb_ct4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [eb_ct4.res, E.eval]
    · simp only [Result.toState_getReg, eb_ct4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct4.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_ct4.res, rv_simp]
  have ne_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
      (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
      simp [hxy, this]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 43460 else pcOf 43452) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct0 (Code.e_ct0_at (im := im)) t0 p0 (by simp [eb_ct0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inl hi0)
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trXE, hi0]) (by simp [trXE, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps im t1 1 1 t ∧
      t.pc = (if lay.val = 0 then pcOf 43460 else pcOf 43453) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct1 (Code.e_ct1_at (im := im)) t1 p1 (by simp [eb_ct1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ _ hlay (by norm_num)]
      by_cases hl0 : lay.val = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay.val = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := by
      exfalso
      have hl : lay = 0 := Fin.ext hl0
      subst hl hi0'
      simp [ClaudeWCT.WCT9.isG, SigGolfCandidate.T3.topIsG] at hG
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trXE, hi0', hl0]) (by simp [trXE, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 43460 else pcOf 43455) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct2 (Code.e_ct2_at (im := im)) t2 p2 (by simp [eb_ct2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [eb_ct2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false :=
      ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inr hm6)
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trXE, hi0', hl0, hm6])
      (by simp [trXE, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : ClaudeWCT.WCT9.chainHigh lay i m = true :=
    ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inl ⟨fun h => hl0 (by rw [h]; rfl), Or.inl ⟨hi0', hm6'⟩⟩)
  have hobl : Oblig.all t3 eb_ct3.res.st.obl := by simp [eb_ct3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound eb_ct3 (Code.e_ct3_at (im := im)) t3 p3 hobl)).of_eq
    (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]) (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [eb_ct3.res, E.eval]
  · simp only [Result.toState_getReg, eb_ct3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [hs, if_pos rfl]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (eb_ct3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (eb_ct3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)

/-! ### Witness stack: the chain step block 49300..49337 (lower G, top G with the top rule, F) -/
theorem pe_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem pe_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem pe_and1 (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

/-- 1041 `jal 49300`, 49300 `beq s0,zero,49306`. -/
theorem sel_spec (hpc : s.pc = pcOf 1041) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 49306 else pcOf 49301) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 49300 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1041 (Code.codeAt_1041 (im := im)) s hpc (by simp [eblk_1041.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_1041.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  refine ⟨_, s0.trans (symRun_sound eblk_49300 (Code.codeAt_49300 (im := im)) t0 p0
    (by simp [eblk_49300.res, rv_simp])), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49300.res, E.eval, CmpOp.eval, r0.get (by simp), h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq hlay (by norm_num)]
    by_cases h0 : lay = 0 <;> simp [h0]
  · have r1 : RegsExcept t0 (eblk_49300.res.toState t0) [] := by
      intro r hr; cases r <;> rfl
    exact (r0.trans r1).mono (by simp)
  · have f1 : Frame t0 (eblk_49300.res.toState t0) (fun _ => False) := by
      intro A _ _; rfl
    exact (f0.trans f1).mono (fun A _ h => by simp_all)

/-- Lower layer: 49301 `andi t1,s3,1`, 49302 `beq t1,zero,49331`. -/
theorem lsel_spec (hpc : s.pc = pcOf 49301) (i : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf 49331 else pcOf 49303) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49301 (Code.codeAt_49301 (im := im)) s hpc (by simp [eblk_49301.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49301.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49301.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49301.res, rv_simp]

/-- Lower G: 49303 `addi t1,zero,6`, 49304 `addi t2,zero,0`, 49305 `jal 49316`. -/
theorem lg_spec (hpc : s.pc = pcOf 49303) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 49316 ∧ t.getReg .x6 = BitVec.ofNat 64 6 ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49303 (Code.codeAt_49303 (im := im)) s hpc (by simp [eblk_49303.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49303.res, E.eval]
  · simp [eblk_49303.res, rv_simp]
  · simp [eblk_49303.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49303.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49303.res, rv_simp]

/-- Top: 49306 `andi t1,s3,1`, 49307 `addi t2,zero,0`, 49308 `bne t1,t2,49331`. -/
theorem tsel_spec (hpc : s.pc = pcOf 49306) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i % 2 = 0 then pcOf 49309 else pcOf 49331) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49306 (Code.codeAt_49306 (im := im)) s hpc (by simp [eblk_49306.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49306.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49306.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49306.res, rv_simp]

/-- Top: 49309 `addi t2,zero,52`, 49310 `blt t2,s3,49331`. -/
theorem tle_spec (hpc : s.pc = pcOf 49309) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 52 < i then pcOf 49331 else pcOf 49311) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49309 (Code.codeAt_49309 (im := im)) s hpc (by simp [eblk_49309.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49309.res, E.eval, CmpOp.eval, rv_simp, h19]
    rw [show (BitVec.ofNat 64 52 : Word) = BitVec.ofNat 64 52 from rfl, ofNat_slt 52 i (by norm_num) hi]
    by_cases h : 52 < i <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49309.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49309.res, rv_simp]

/-- T51 top G: 49311 `j 54543`, GT 54543..54552 (`t1 := 4 - [27 <= i < 48] + [i = 48]`, 7 for chain 0), 49315
`ld t2,24(t3)`: the step at which the G chain writes LOW (`gTerm`: `maxDigit 0 i - 1`; chain 0 never) and the header
high word. -/
def gTerm (i : Nat) : Nat := if i = 0 then 7 else SigGolfCandidate.T3.maxDigit 0 i - 1
def gtK (i : Nat) : Nat := if i = 0 then 12 else 11
theorem tcap_spec (hpc : s.pc = pcOf 49311) (i : Nat) (hi : i ≤ 52) (hev : i % 2 = 0)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (gtK i) (gtK i) t ∧ t.pc = pcOf 49316 ∧
      t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54543 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_49311 (Code.codeAt_49311 (im := im)) s hpc (by simp [eblk_49311.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_49311.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 8 8 t ∧
      t.pc = (if i = 0 then pcOf 54551 else pcOf 54552) ∧
      t.getReg .x6 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i - 1) ∧
      RegsExcept t0 t [.x6, .x7] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_gt0 (Code.e_gt0_at (im := im)) t0 p0 (by simp [eb_gt0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_gt0.res, E.eval, CmpOp.eval, g19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
      by_cases h0 : i = 0 <;> simp [h0]
    · simp only [Result.toState_getReg, eb_gt0.res, rv_simp, g19]
      interval_cases i <;> first | decide | (exfalso; omega)
    · ex_regs eb_gt0.res
    · intro A _ _; simp [eb_gt0.res, rv_simp]
  obtain ⟨t2, k2, s2, hk2, p2, x2, r2, f2⟩ : ∃ t k, Steps im t1 k k t ∧ k = (if i = 0 then 2 else 1) ∧
      t.pc = pcOf 49315 ∧ t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      RegsExcept t1 t [.x6] ∧ Frame t1 t (fun _ => False) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at p1
      refine ⟨_, 2, symRun_sound eb_gt1 (Code.e_gt1_at (im := im)) t1 p1 (by simp [eb_gt1.res, rv_simp]),
        by rw [if_pos h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt1.res, E.eval]
      · simp [eb_gt1.res, rv_simp, gTerm, h0]
      · ex_regs eb_gt1.res
      · intro A _ _; simp [eb_gt1.res, rv_simp]
    · rw [if_neg h0] at p1
      refine ⟨_, 1, symRun_sound eb_gt2 (Code.e_gt2_at (im := im)) t1 p1 (by simp [eb_gt2.res, rv_simp]),
        by rw [if_neg h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt2.res, E.eval]
      · simp only [Result.toState_getReg, eb_gt2.res, rv_simp, x1, gTerm, if_neg h0]
      · intro r hr; cases r <;> rfl
      · intro A _ _; rfl
  have r02 : RegsExcept s t2 [.x6, .x7] := ((r0.trans r1).trans r2).mono (by decide)
  have v28 : t2.getReg .x28 = BitVec.ofNat 64 CHAIN := by rw [r02.get (by simp)]; exact h28
  have hobl : Oblig.all t2 eblk_49315.res.st.obl := by
    simp only [eblk_49315.res]
    t3n [v28, CHAIN]
    try norm_num
  have sw := symRun_sound eblk_49315 (Code.codeAt_49315 (im := im)) t2 p2 hobl
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)
  refine ⟨_, (((s0.trans s1).trans s2).trans sw).of_eq (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res])
    (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res]), by simp [eblk_49315.res, E.eval], ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_getReg, eblk_49315.res, rv_simp]; exact x2
  · rw [← f02.get (A := CHAIN + 24) (by decide) (by simp)]
    simp only [Result.toState_getReg, eblk_49315.res, rv_simp]
    t3n [v28, CHAIN]
  · have rw' : RegsExcept t2 (eblk_49315.res.toState t2) [.x7] := by
      intro r hr; simp at hr; cases r <;> simp_all [eblk_49315.res, rv_simp] <;> rfl
    exact (r02.trans rw').mono (by simp)
  · intro A hA _
    rw [show (eblk_49315.res.toState t2).getMem (BitVec.ofNat 64 A) = t2.getMem (BitVec.ofNat 64 A) by
      simp [eblk_49315.res, rv_simp]]
    exact (f02.get hA (by simp))

/-- The G body 49316..49326 (and 49327 on the terminal step `m = T`): `CHAIN+64 := CHAIN+16`, `CHAIN+72 := t2`,
pads, HASH arguments. -/
theorem g_spec (hpc : s.pc = pcOf 49316) (m T : Nat) (Y : Word)
    (hm : m < 2 ^ 63) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = Y)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (11 + (if m = T then 1 else 0)) (11 + (if m = T then 1 else 0)) t ∧ t.pc = pcOf 49328 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = T then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12, .x30] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s eblk_49316.res.st.obl := by
    simp only [eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  have st := symRun_sound eblk_49316 (Code.codeAt_49316 (im := im)) s hpc hobl
  set u := eblk_49316.res.toState s with hu
  have upc : u.pc = (if m = T then pcOf 49327 else pcOf 49328) := by
    simp only [hu, Result.toState_pc, eblk_49316.res, E.eval, CmpOp.eval, h20, h6]
    rw [pe_ne (by omega) (by omega)]
    by_cases hm6 : m = T <;> simp [hm6]
  have ur : RegsExcept s u [.x10, .x11, .x12, .x30] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, eblk_49316.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    simp only [hu, Result.toState_getMem, eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131560 by omega, show ¬ A = 131568 by omega, show ¬ A = 131576 by omega,
      show ¬ A = 131584 by omega, show ¬ A = 131592 by omega, show ¬ A = 131552 by omega, if_false]
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp] <;> rfl
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, eblk_49316.res]
      t3n [h28, h7, CHAIN, Nat.reduceLeDiff, and_true]
  by_cases hm6 : m = T
  · rw [if_pos hm6] at upc
    have hobl6 : Oblig.all u eblk_49327.res.st.obl := by simp [eblk_49327.res, rv_simp]
    have st6 := symRun_sound eblk_49327 (Code.codeAt_49327 (im := im)) u upc hobl6
    refine ⟨_, (st.trans st6).of_eq (by simp [hm6, eblk_49316.res, eblk_49327.res])
      (by simp [hm6, eblk_49316.res, eblk_49327.res]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [eblk_49327.res, E.eval]
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u10
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u11
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp, if_pos hm6, ur.get (show Reg.x28 ∉ _ by simp), h28]
      rfl
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.2
    · intro r hr
      rw [show (eblk_49327.res.toState u).getReg r = u.getReg r by
        cases r <;> simp_all [eblk_49327.res, rv_simp] <;> rfl]
      exact ur r hr
    · intro A hA hn
      rw [show (eblk_49327.res.toState u).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) by
        simp [eblk_49327.res, rv_simp]]
      exact uf A hA hn
  · rw [if_neg hm6] at upc
    refine ⟨u, st.of_eq (by simp [hm6, eblk_49316.res]) (by simp [hm6, eblk_49316.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg hm6]; exact u12

/-- The F body 49331..49335: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec (hpc : s.pc = pcOf 49331) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 49336 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s eblk_49331.res.st.obl := by
    simp only [eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  refine ⟨_, symRun_sound eblk_49331 (Code.codeAt_49331 (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49331.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49331.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131520 by omega, show ¬ A = 131528 by omega, if_false]

/-- 49329 `addi s4,s4,1`, 49330 `jal 1031`. -/
theorem gtail_spec (hpc : s.pc = pcOf 49329) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49329 (Code.codeAt_49329 (im := im)) s hpc (by simp [eblk_49329.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [eblk_49329.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49329.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49329.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49329.res, rv_simp]

theorem rl1049_spec (hpc : s.pc = pcOf 1049) (lay : T3.Layer) (i : Nat) (hi : i < 2 ^ 59)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (slK lay i) (slK lay i) t ∧ t.pc = pcOf 1052 ∧
      t.getReg .x28 = BitVec.ofNat 64 (slotOff lay i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42758 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1049 (Code.codeAt_1049 (im := im)) s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1049.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g19 : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), h19]
  obtain ⟨t2, s2, p2, x28, r2, f2⟩ : ∃ t, Steps im t1 2 2 t ∧
      t.pc = pcOf 42760 ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧
      RegsExcept t1 t [.x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slA (Code.e_slA_at (im := im)) t1 p1 (by simp [eb_slA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_slA.res, E.eval]
    · simp only [Result.toState_getReg, eb_slA.res, rv_simp, g19]
      t3n []; congr 1; ring
    · ex_regs eb_slA.res
    · intro A _ _; simp [eb_slA.res, rv_simp]
  have g19' : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19]
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 1 1 t ∧
      t.pc = (if i = 0 then pcOf 42764 else pcOf 42761) ∧ RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slB (Code.e_slB_at (im := im)) t2 p2 (by simp [eb_slB.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_slB.res, E.eval, CmpOp.eval, g19']
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq i 0 (by omega) (by norm_num)]
      by_cases hc : i = 0 <;> simp [hc]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  by_cases hi0 : i = 0
  · rw [if_pos hi0] at p3
    obtain ⟨t4, s4, p4, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1052 ∧ RegsExcept t3 t [] ∧
        Frame t3 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slZ (Code.e_slZ_at (im := im)) t3 p3 (by simp [eb_slZ.res, rv_simp]), ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slZ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [r4.get (by decide), r3.get (by decide), x28, slotOff, if_pos hi0, hi0],
      (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
  · rw [if_neg hi0] at p3
    have y28 : t3.getReg .x28 = BitVec.ofNat 64 (16 * i) := by rw [r3.get (by decide), x28]
    obtain ⟨t4, s4, p4, z28, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1052 ∧
        t.getReg .x28 = BitVec.ofNat 64 (16 * i + 16) ∧ RegsExcept t3 t [.x28] ∧ Frame t3 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slN (Code.e_slN_at (im := im)) t3 p3 (by simp [eb_slN.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slN.res, E.eval]
      · simp only [Result.toState_getReg, eb_slN.res, rv_simp, y28, ofNat_add_ofNat]
      · ex_regs eb_slN.res
      · intro A _ _; simp [eb_slN.res, rv_simp]
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [z28, slotOff, if_neg hi0], (((r1.trans r2).trans r3).trans r4).mono (by decide),
      (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1052_spec (hpc : s.pc = pcOf 1052) (i x : Nat) (hx8 : x % 8 = 0) (hx : LEAFPK + x + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 x) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + x ∨ A = LEAFPK + x + 8) := by
  refine ⟨_, symRun_sound eblk_1052 (Code.codeAt_1052 (im := im)) s hpc (by
      simp only [eblk_1052.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, ofNat_add_ofNat,
        show (132616#64 : Word) = BitVec.ofNat 64 132616 from rfl,
        show (132608#64 : Word) = BitVec.ofNat 64 132608 from rfl, accessValid_iff, MEMORY_BYTES,
        toNat_ofNat_lt (show x + 132616 < 2 ^ 64 by simp only [LEAFPK] at hx; omega),
        toNat_ofNat_lt (show x + 132608 < 2 ^ 64 by simp only [LEAFPK] at hx; omega)]
      simp only [LEAFPK] at hx; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1052.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1052.res, rv_simp, h19, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · ex_regs eblk_1052.res
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, eblk_1052.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

theorem rl1063_spec (hpc : s.pc = pcOf 1063) (n : Nat) (hn : n < 2 ^ 32)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 1072 ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1063 (Code.codeAt_1063 (im := im)) s hpc (by simp [eblk_1063.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1063.res, E.eval]
  · simp [eblk_1063.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1063.res, rv_simp, h26]
    have e1 : (BitVec.ofNat 64 n + 1#64) <<< ((4#64 : Word).toNat % 64) + 63#64 =
        BitVec.ofNat 64 (16 * (n + 1) + 63) := by
      rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
        show (63#64 : Word) = BitVec.ofNat 64 63 from rfl, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat]
      congr 1; ring
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt (show 16 * (n + 1) + 63 < 2 ^ 64 by omega),
      toNat_ofNat_lt (show (16 * (n + 1) + 63) / 64 * 64 < 2 ^ 64 by omega),
      show (18446744073709551552#64 : Word).toNat = (2 ^ 58 - 1) * 2 ^ 6 from rfl]
    have key : ∀ x : Nat, x < 2 ^ 64 → x &&& ((2 ^ 58 - 1) * 2 ^ 6) = x / 64 * 64 := by
      intro x hx
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_mul_two_pow, show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_mul_two_pow,
        Nat.testBit_two_pow_sub_one]
      by_cases hk : 6 ≤ k
      · simp only [hk, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
        by_cases hk2 : k - 6 < 58
        · simp [hk2, show k - 6 + 6 = k by omega]
        · simp only [hk2, decide_false, Bool.and_false]
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      · simp [hk]
    exact key _ (by omega)
  · simp [eblk_1063.res, rv_simp]
  · ex_regs eblk_1063.res
  · intro A _ _; simp [eblk_1063.res, rv_simp]

theorem rl1073_spec (hpc : s.pc = pcOf 1073) (P n : Nat) (hP : P + 16 * n < 2 ^ 64)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 P) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 (P + 16 * n) ∧ RegsExcept s t [.x20, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1073 (Code.codeAt_1073 (im := im)) s hpc (by simp [eblk_1073.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1073.res, E.eval]
  · simp [eblk_1073.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1073.res, rv_simp, h16, h26]
    t3n []; congr 1; ring
  · ex_regs eblk_1073.res
  · intro A _ _; simp [eblk_1073.res, rv_simp]

theorem rl1076_spec (hpc : s.pc = pcOf 1076) (j hh : Nat) (hj : j < 2 ^ 63) (hh' : hh < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if hh ≤ j then pcOf 1143 else pcOf 1077) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1076 (Code.codeAt_1076 (im := im)) s hpc (by simp [eblk_1076.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1076.res, E.eval, CmpOp.eval, h20, h15]
    rw [ex_slt j hh hj hh']
    by_cases hc : hh ≤ j
    · simp [hc, show ¬ j < hh by omega]
    · simp [hc, show j < hh by omega]
  · ex_regs eblk_1076.res
  · intro A _ _; simp [eblk_1076.res, rv_simp]

theorem rl1077_spec (hpc : s.pc = pcOf 1077) (leaf j : Nat) (hl : leaf < 2 ^ 64) (hj : j < 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if leaf / 2 ^ j % 2 = 0 then pcOf 1099 else pcOf 1080) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1077 (Code.codeAt_1077 (im := im)) s hpc (by simp [eblk_1077.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1077.res, E.eval, CmpOp.eval, BinOp.eval, h18, h20]
    rw [toNat_ofNat_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj, ofNat_shr _ _ hl, ofNat_and1,
      show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ 0 (by omega) (by norm_num)]
    by_cases hc : leaf / 2 ^ j % 2 = 0
    · simp [hc]
    · simp [hc]
  · ex_regs eblk_1077.res
  · intro A _ _; simp [eblk_1077.res, rv_simp]

theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 19 19 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 M) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M ∨ A = M + 8 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1080 (Code.codeAt_1080 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1080.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [show (131584 : Nat) = NODE from rfl, show (131592 : Nat) = NODE + 8 from rfl]; exact ex_ne _ _ (by omega) (by omega) (by omega))
        | skip
  · simp [Result.toState_pc, eblk_1080.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1080.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1080.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1080.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem rl1105_spec (hpc : s.pc = pcOf 1105) (X P : Nat) (hX : X = NOUT ∨ X = NOUT + 16) (hP8 : P % 8 = 0)
    (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) (h22 : s.getReg .x22 = BitVec.ofNat 64 P) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 X) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (X + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  have hX' : 131648 ≤ X ∧ X ≤ 131664 ∧ X % 8 = 0 := by rcases hX with h | h <;> rw [h] <;> decide
  refine ⟨_, symRun_sound eb_lcD (Code.e_lcD_at (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eb_lcD.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h29, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    repeat' apply And.intro
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | skip
  · simp [Result.toState_pc, eb_lcD.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eb_lcD.res, NODE, NOUT]
      t3n [h22, h29]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eb_lcD.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eb_lcD.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
/-- C2 (FULL): the bit-0 branch (current value = left input). Lower layers read the high half of the node output
(`NOUT + 16`, trampoline at 43462), the top layer the low half. -/
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P)
    (hP' : P + 16 ≤ 0x7000 + 5616) (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 22 22 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M + 48 ∨ A = M + 56 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  obtain ⟨t1, s1, p1, m48, m56, r1, f1⟩ : ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 43462 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun A => A = M + 48 ∨ A = M + 56) := by
    refine ⟨_, symRun_sound eblk_1099 (Code.codeAt_1099 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [eblk_1099.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
        h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
      repeat' apply And.intro
      all_goals first
          | exact ex_valid _ (by omega) (by omega)
          | exact ex_ne _ _ (by omega) (by omega) (by omega)
          | skip
    · simp [Result.toState_pc, eblk_1099.res, E.eval]
    iterate 2
      · simp only [Result.toState_getMem, eblk_1099.res]
        t3n [h22, h24]
        all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
    · ex_regs eblk_1099.res
    · intro A hA hn
      simp only [Result.toState_getMem, eblk_1099.res]
      t3n [h24]
      rw [if_neg (by omega), if_neg (by omega)]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  obtain ⟨t2, s2, p2, x29, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = pcOf 43465 ∧ t.getReg .x29 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t1 t [.x29] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcA (Code.e_lcA_at (im := im)) t1 p1 (by simp [eb_lcA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcA.res, E.eval]
    · simp [eb_lcA.res, rv_simp]
    · ex_regs eb_lcA.res
    · intro A _ _; simp [eb_lcA.res, rv_simp]
  obtain ⟨t3, s3, p3, y29, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧
      t.pc = pcOf 1105 ∧ t.getReg .x29 = BitVec.ofNat 64 (NOUT + hiOff lay) ∧
      RegsExcept t2 t [.x29] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcB (Code.e_lcB_at (im := im)) t2 p2 (by simp [eb_lcB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcB.res, E.eval]
    · simp only [Result.toState_getReg, eb_lcB.res, rv_simp, x29, hiOff, ofNat_add_ofNat]
    · ex_regs eb_lcB.res
    · intro A _ _; simp [eb_lcB.res, rv_simp]
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 P := by
    rw [r3.get (by decide), r2.get (by decide), r1.get (by decide), h22]
  obtain ⟨t4, s4, p4, n0, n8, n48, n56, r4, f4⟩ := rl1105_spec (im := im) t3 p3 (NOUT + hiOff lay) P
    (by unfold hiOff; simp) hP8 hP hP' y29 g22
  have f13 : Frame s t3 (fun A => A = M + 48 ∨ A = M + 56) :=
    ((f1.trans f2).trans f3).mono (fun A _ h => by rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim)
  have hoff : hiOff lay ≤ 16 := by unfold hiOff; omega
  refine ⟨t4, ((s1.trans s2).trans s3).trans s4 |>.of_eq rfl rfl, p4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m48]
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m56]
  · rw [n0, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n8, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n48, f13.get (by omega) (by omega)]
  · rw [n56, f13.get (by omega) (by omega)]
  · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
  · exact (f13.trans f4).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)
theorem rl1119_spec (hpc : s.pc = pcOf 1119) (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12) (htopl : lay = 0 → leaf < 2 ^ hh)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (hh - j - 1)) :
    ∃ t, Steps im s (hdrK lay) (hdrK lay) t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  set heap := 2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 64 := by
    have : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  obtain ⟨t1, s1, p1, x13, r1, f1⟩ : ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42765 ∧
      t.getReg .x13 = BitVec.ofNat 64 heap ∧
      RegsExcept s t [.x13, .x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrA (Code.e_hdrA_at (im := im)) s hpc (by simp [eb_hdrA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrA.res, E.eval]
    · simp only [Result.toState_getReg, eb_hdrA.res]
      t3n [h9, h15, h20, h18, h28]
      have e1 : (BitVec.ofNat 64 (hh - j - 1)).toNat % 64 = hh - j - 1 := by
        rw [toNat_ofNat_lt (show hh - j - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [BitVec.toNat_ofNat] at e1
      have e2 : (j + 1) % 18446744073709551616 % 64 = j + 1 := by omega
      have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hq : leaf / 2 ^ (j + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
      rw [e1, e2, ofNat_shr _ _ (by omega), Nat.one_mul, ofNat_add_ofNat]
    · ex_regs eb_hdrA.res
    · intro A _ _; simp [eb_hdrA.res, rv_simp]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  obtain ⟨t2, s2, p2, x7, x6, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if lay = 0 then pcOf 42776 else pcOf 42768) ∧
      t.getReg .x7 = 0 ∧
      t.getReg .x6 = BitVec.ofNat 64 heap ∧ RegsExcept t1 t [.x6, .x7] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrB (Code.e_hdrB_at (im := im)) t1 p1 (by simp [eb_hdrB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hdrB.res, E.eval, CmpOp.eval, g8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0 <;> simp [h0]
    · simp [eb_hdrB.res, rv_simp]
    · simp only [Result.toState_getReg, eb_hdrB.res, rv_simp, x13]
    · ex_regs eb_hdrB.res
    · intro A _ _; simp [eb_hdrB.res, rv_simp]
  have g13 : t2.getReg .x13 = BitVec.ofNat 64 heap := by rw [r2.get (by decide), x13]
  obtain ⟨t3, s3, p3, y6, y7, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 1 else 13) (if lay = 0 then 1 else 13) t ∧
      t.pc = pcOf 1129 ∧ t.getReg .x6 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getReg .x7 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      RegsExcept t2 t [.x6, .x7, .x30] ∧ Frame t2 t (fun _ => False) := by
    by_cases h0 : lay = 0
    · subst h0
      rw [if_pos rfl] at p2
      have hlf := htopl rfl
      have hheap1 : 1 ≤ heap := by
        rw [hheap]; exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
      have hheap2 : heap < 4096 := by
        have e : 2 ^ hh = 2 ^ (j + 1) * 2 ^ (hh - j - 1) := by rw [← Nat.pow_add]; congr 1; omega
        have hq : leaf / 2 ^ (j + 1) < 2 ^ (hh - j - 1) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hlf
        have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h11 : (2 : Nat) ^ 11 = 2048 := by norm_num
        rw [hheap]
        rw [h11] at hp
        generalize 2 ^ (hh - j - 1) = X at hq hp ⊢
        generalize leaf / 2 ^ (j + 1) = Y at hq ⊢
        omega
      obtain ⟨wlo, whi⟩ := merkleTweak_words_top tree heap hheap1 hheap2
      refine ⟨_, (symRun_sound eb_hdrD (Code.e_hdrD_at (im := im)) t2 p2 (by simp [eb_hdrD.res, rv_simp])).of_eq (by simp [eb_hdrD.res])
        (by simp [eb_hdrD.res]), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hdrD.res, E.eval]
      · rw [wlo]; simp only [Result.toState_getReg, eb_hdrD.res, rv_simp, x6]
      · rw [whi]; simp only [Result.toState_getReg, eb_hdrD.res, rv_simp, x7]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    · rw [if_neg h0] at p2
      have g8' : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [r2.get (by decide), g8]
      have g9' : t2.getReg .x9 = BitVec.ofNat 64 tree := by rw [r2.get (by decide), g9]
      obtain ⟨u, su, pu, uor, u13, ru, fu⟩ : ∃ u, Steps im t2 8 8 u ∧ u.pc = pcOf 43467 ∧
          (u.getReg .x6 ||| u.getReg .x30) = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
          u.getReg .x13 = BitVec.ofNat 64 heap ∧ RegsExcept t2 u [.x6, .x30] ∧ Frame t2 u (fun _ => False) := by
        refine ⟨_, symRun_sound eb_hdrC (Code.e_hdrC_at (im := im)) t2 p2 (by simp [eb_hdrC.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_hdrC.res, E.eval]
        · simp only [Result.toState_getReg, eb_hdrC.res]
          t3n [g8', g9']
          unfold Keygen.nodeLo
          rw [if_neg h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hl' : BitVec.ofNat 64 ((lay + 18446744073709551615) * 281474976710656) =
              BitVec.ofNat 64 ((lay - 1) * 281474976710656) := by
            apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
          rw [hl', show (513#64) = BitVec.ofNat 64 513 from rfl,
            ofNat_or_disjoint 513 (tree * 65536) 16 (by decide) (by omega),
            ofNat_or_disjoint' _ ((lay - 1) * 281474976710656) 48 (by omega) (by omega),
            show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
            ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
          unfold T3.hyperWord
          congr 1
          rw [Nat.mod_eq_of_lt htree, Nat.mod_eq_of_lt (by omega : lay - 1 < 256)]
          omega
        · simp only [Result.toState_getReg, eb_hdrC.res, rv_simp, g13]
        · ex_regs eb_hdrC.res
        · intro A _ _; simp [eb_hdrC.res, rv_simp]
      refine ⟨_, (su.trans (symRun_sound eb_hdrT (Code.e_hdrT_at (im := im)) u pu (by simp [eb_hdrT.res, rv_simp]))).of_eq
        (by simp [h0, eb_hdrT.res]) (by simp [h0, eb_hdrT.res]), ?_, ?_, ?_, ?_, ?_⟩
      · exact eb_hdrT_pc u
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_low, eb_hdrT_x6, uor, u13]
        unfold Keygen.nodeLo ClaudeWCT.WCT9.lowerK
        rw [if_neg h0, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc, ofNat_add_ofNat,
          Nat.add_comm heap 1407]
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_high, eb_hdrT_x7]
      · exact (ru.trans (eb_hdrT_regs u)).mono (by decide)
      · exact (fu.trans (eb_hdrT_frame u)).mono (fun A _ h => by simp_all)
  obtain ⟨t4, s4, p4, m16, m24, x10, x11, x12, r4, f4⟩ : ∃ t, Steps im t3 9 9 t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t3 t [.x10, .x11, .x12, .x28] ∧ Frame t3 t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
    refine ⟨_, symRun_sound eb_hdrE (Code.e_hdrE_at (im := im)) t3 p3 (by simp [eb_hdrE.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrE.res, E.eval]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y6]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y7]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · exact eb_hdrE_regs t3
    · intro A hA hn
      simp only [NODE] at hn
      simp only [Result.toState_getMem, eb_hdrE.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hdrK; split_ifs <;> simp_all)
    (by unfold hdrK; split_ifs <;> simp_all), p4, m16, m24, x10, x11, x12,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1143_spec (hpc : s.pc = pcOf 1143) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_1143 (Code.codeAt_1143 (im := im)) s hpc (by simp [eblk_1143.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1143.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · ex_regs eblk_1143.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_1143.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
theorem fetch_49328 (hpc : s.pc = pcOf 49328) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_49328 (im := im)).fetch s hpc).trans rfl
theorem fetch_49336 (hpc : s.pc = pcOf 49336) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_49336 (im := im)).fetch s hpc).trans rfl
theorem fetch_1072 (hpc : s.pc = pcOf 1072) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_1072 (im := im)).fetch s hpc).trans rfl
theorem fetch_1138 (hpc : s.pc = pcOf 1138) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_1138 (im := im)).fetch s hpc).trans rfl
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_packed : PackedBlocks.Code Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_bc : BCBlocks.Code Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_code : Code Images.expandImage := by
  constructor <;> first
    | (apply codeAt_expand_current_chunk <;> decide +kernel)
    | (apply codeAt_t51_at <;> decide)
    | (apply codeAt_expand_last <;> decide +kernel)

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
section tb
variable {image : Image} {sk : BitVec 256}
theorem tb_shortHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem tb_mapM_idx {γ δ : Type} (f : γ → T3.M δ) (idx : γ → Nat) (W : Nat) (Inv : List δ → MachineState → Prop) :
    ∀ (xs : List γ) (pre : List δ) {s : MachineState}, xs.map idx = List.range' pre.length xs.length →
    (∀ x ∈ xs, ∀ (pre' : List δ) t, pre'.length = idx x → Inv pre' t →
      TBSim image sk t W (f x) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s → TBSim image sk s (xs.length * W) (xs.mapM f) (fun ds u => ds.length = xs.length ∧ Inv (pre ++ ds) u)
  | [], pre, s, _, _, h0 => by
    simpa using TBSim.pure (image := image) (sk := sk) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | x :: xs, pre, s, hidx, hb, h0 => by
    rw [List.mapM_cons]
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    have h1 := hb x (by simp) pre s hidx.1.symm h0
    have key : ∀ d t, Inv (pre ++ [d]) t → TBSim image sk t (xs.length * W)
        (do let ds ← xs.mapM f; Pure.pure (d :: ds)) (fun ds u => ds.length = xs.length + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := tb_mapM_idx f idx W Inv xs (pre ++ [d]) (by simpa using hidx.2) (fun y hy => hb y (by simp [hy])) ht
      exact (TBSim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => TBSim.pure ⟨by simp [hu.1], by simpa using hu.2⟩)).mono (by omega) (fun _ _ h => h)
    exact (TBSim.bind h1 key).mono (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => h)
theorem tb_mapM_finRange {δ : Type} (n : Nat) (f : Fin n → T3.M δ) (W : Nat) (Inv : List δ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) (pre : List δ) t, pre.length = i.val → Inv pre t →
      TBSim image sk t W (f i) (fun d u => Inv (pre ++ [d]) u)) {s : MachineState} (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.finRange n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  have := tb_mapM_idx f Fin.val W Inv (List.finRange n) [] (by rw [finRange_map_val]; simp)
    (fun x _ pre' t h1 h2 => hbody x pre' t h1 h2) h0
  simpa using this
theorem tb_foldlM_finRange {γ : Type} (n : Nat) (f : γ → Fin n → T3.M γ) (init : γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (n * W) ((List.finRange n).foldlM f init) (Inv n) := by
  have gen : ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
    intro xs
    induction xs with
    | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
    | cons x xs ih =>
      intro k acc t hidx ht
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
      rw [List.foldlM_cons]
      have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
      rw [hidx.1] at h1
      refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
        (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using h)
      have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
      rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
  have := gen (List.finRange n) 0 init s (by rw [finRange_map_val]; simp) h0
  simpa using this
theorem tb_foldlM_vals {γ : Type} {n : Nat} (f : γ → Fin n → T3.M γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1))) :
    ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
  intro xs
  induction xs with
  | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
  | cons x xs ih =>
    intro k acc t hidx ht
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    rw [List.foldlM_cons]
    have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
    rw [hidx.1] at h1
    refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
      (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
    rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
theorem chainInput_length' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, T3.zero16]
theorem wordsOf_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (pad64 (chainInput lay tree leaf i step v)) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_length'])]
  exact Keygen.Packed.wordsOf_chainInput lay tree leaf i step v
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x9 : t.getReg .x9 = BitVec.ofNat 64 tree
  x18 : t.getReg .x18 = BitVec.ofNat 64 leaf
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
/-- Pairing stage 1: a chain step writes the header words and `CHAIN+32 .. CHAIN+112` (G: pads, header copy and the
interior output at `CHAIN+32`; F: the pad `CHAIN+32/40`, the output at `CHAIN+48`). -/
def StepW (A : Nat) : Prop := (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x18 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x9 := by rw [hr.get hl.2.2.1]; exact h.x9
  x18 := by rw [hr.get hl.2.2.2.1]; exact h.x18
  x19 := by rw [hr.get hl.2.2.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (lay : T3.Layer) (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8 ∨ A = W + 48 ∨ A = W + 56
/-- T51: the top chain caps of KMAX (`maxDigit 0 i`; `n4` is unused), lower layers 7. -/
def endpoint (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7
/-- Extra cycles of the cap selection on the top (1030 `j 1158`, KMAX). -/
def endpointExtra (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then 1 + SharedRecover.kmaxSteps i else 0
/-- Cycle budget of one chain step: the T51 top G step runs GT (+7 cycles). -/
def stepW (lay : Layer) : Nat := if lay = 0 then 67 else 60
def ChW (lay : T3.Layer) (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff lay c ∨ A = LEAFPK + slotOff lay c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
theorem not_ChW_of {lay : T3.Layer} {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 112 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW lay WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
theorem not_ChW_hdr {lay : T3.Layer} {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24)
    (hk : k ≤ 54) : ¬ ChW lay WC k A := by
  rcases h with h | h
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff lay j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW lay WC ends.length)
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem tb_halfHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat} (high : Bool)
    {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (ClaudeWCT.WCT9.halfOf high a)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (ClaudeWCT.WCT9.halfHash high input >>= f) Q := by
  rw [ClaudeWCT.WCT9.halfHash_eq, bind_assoc]
  simp only [pure_bind]
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
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
/-- The step at which a G chain writes LOW (T51 top: `gTerm`; lower: 6). -/
def gTermL (lay : Layer) (i : Nat) : Nat := if lay = 0 then SharedRecover.gTerm i else SigGolfCandidate.T3.maxDigit lay i - 1
/-- Witness stack: on a G chain (lower odd, or top even `≤ 50`) the step keeps the high half exactly when it is not the
step `gTermL` (T51: `maxDigit - 1`; top chain 0 keeps the high half on every step). -/
theorem gHigh_eq {lay : Layer} {i m : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true)
    (hm : m < SigGolfCandidate.T3.maxDigit lay i) :
    ClaudeWCT.WCT9.chainHigh lay i m = decide (m ≠ gTermL lay i) := by
  apply Bool.eq_iff_iff.mpr
  rw [ClaudeWCT.WCT9.chainHigh_eq_true, decide_eq_true_iff]
  rcases ClaudeWCT.WCT9.isG_eq_true.mp hG with ⟨hl, hi⟩ | ⟨hl, hi, hi50⟩
  · have hmd : SigGolfCandidate.T3.maxDigit lay i = 7 := by simp [SigGolfCandidate.T3.maxDigit, hl]
    have hg : gTermL lay i = 6 := by simp [gTermL, hl, hmd]
    rw [hmd] at hm
    rw [hg]
    constructor
    · rintro (⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h, _, _⟩)
      · omega
      · omega
      · exact absurd h hl
    · intro h; exact Or.inl ⟨hl, Or.inr ⟨hi, by omega⟩⟩
  · subst hl
    have hg : gTermL 0 i = SharedRecover.gTerm i := by simp [gTermL]
    rw [hg]
    unfold SharedRecover.gTerm
    constructor
    · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · exact absurd rfl h
      · by_cases h0 : i = 0
        · rw [if_pos h0]
          have : SigGolfCandidate.T3.maxDigit 0 i = 5 := by subst h0; rfl
          omega
        · rw [if_neg h0]; omega
    · intro h
      refine Or.inr ⟨rfl, ⟨hi, hi50⟩, ?_⟩
      by_cases h0 : i = 0
      · exact Or.inr h0
      · rw [if_neg h0] at h; exact Or.inl (by omega)

/-- Witness stack: one chain step (loop head 1031, header 1032..1040, the step block 49300..49337 and, on the F
path, the C3 tail) computes `halfHash (chainHigh) (chainInputW)`; at most 60 instructions + HASH. -/
theorem chain_step (lay : Layer) (tree leaf i st e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hst : st < e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t (stepW lay) (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, a28, m16, m24, r2, f2⟩ := rl1032_spec (im := im) t1 p1 lay tree leaf i st hr hf hi (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact hc.x9) (by rw [r1.get (by simp)]; exact hc.x18)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have r12 : RegsExcept t t2 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (r1.trans r2).mono (by simp)
  have g2 : ∀ r, r ∉ stepRegs → t2.getReg r = t.getReg r := fun r hr =>
    r12.get (not_mem_of_sub (by simp [stepRegs]) hr)
  obtain ⟨u0, s0, p0, r0, f0⟩ := sel_spec (im := im) t2 p2 lay.val (by omega)
    (by rw [g2 _ (by simp [stepRegs])]; exact hc.x8)
  have g19 : u0.getReg .x19 = BitVec.ofNat 64 i := by
    rw [r0.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x19
  have hK := expHdrK_le lay
  have fin_frame : ∀ {w : MachineState}, Frame t2 w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) →
      Frame t w StepW := fun hw => (f12.trans hw).mono (fun A _ h => by
        unfold StepW; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h)
  rw [show ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v) =
    (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)
      >>= pure) by rw [bind_pure]]
  by_cases hGb : ClaudeWCT.WCT9.isG lay i = true
  · -- G path: `value | header | 0 | 0` at CHAIN+48
    obtain ⟨u, k1, su, hk1, upc, u6, u7, ur, uf⟩ : ∃ u k1, Steps im t2 k1 k1 u ∧ expHdrK lay + k1 + 23 ≤ stepW lay ∧
        u.pc = pcOf 49316 ∧ u.getReg .x6 = BitVec.ofNat 64 (gTermL lay i) ∧
        u.getReg .x7 = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
        RegsExcept t2 u [.x6, .x7] ∧ Frame t2 u (fun _ => False) := by
      rcases ClaudeWCT.WCT9.isG_eq_true.mp hGb with ⟨hl, hi2⟩ | ⟨hl, hi2, hi52⟩
      · have hl' : lay.val ≠ 0 := fun h => hl (Fin.ext h)
        rw [if_neg hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        rw [if_neg (by omega)] at p1'
        obtain ⟨u2, q2, p2', x6', x7', r2', f2'⟩ := lg_spec (im := im) u1 p1'
        refine ⟨u2, 7, s0.trans (q1.trans q2), by unfold stepW; rw [if_neg hl]; have := expHdrK_le lay; unfold expHdrK at this ⊢; split_ifs at this ⊢ <;> omega, p2', ?_, ?_, ?_, ?_⟩
        · rw [x6']; simp [gTermL, SigGolfCandidate.T3.maxDigit, hl]
        · rw [x7', Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi (by omega)]
        · exact ((r0.trans r1').trans r2').mono (by simp)
        · exact ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
      · have hl' : lay.val = 0 := by rw [hl]; rfl
        rw [if_pos hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        rw [if_pos hi2] at p1'
        obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
          (by rw [r1'.get (by simp)]; exact g19)
        rw [if_neg (by omega)] at p2'
        obtain ⟨u3, q3, p3', x6', x7', r3', f3'⟩ := tcap_spec (im := im) u2 p2' i (by omega) hi2
          (by rw [r2'.get (by simp), r1'.get (by simp)]; exact g19)
          (by rw [r2'.get (by simp), r1'.get (by simp), r0.get (by simp)]; exact a28)
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl']
        refine ⟨u3, _, ((s0.trans q1).trans q2).trans q3, by rw [hK0]; unfold stepW gtK; rw [if_pos hl]; split_ifs <;> omega,
          p3', ?_, ?_, ?_, ?_⟩
        · rw [x6', hl]; simp [gTermL]
        · have f02 : Frame t2 u2 (fun _ => False) :=
            ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
          rw [x7', f02.get (by decide) (by simp), m24]
        · exact (((r0.trans r1').trans r2').trans r3').mono (by simp)
        · exact (((f0.trans f1').trans f2').trans f3').mono (fun A _ h => by simp_all)
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t2.getReg r := fun r hr => ur.get hr
    have hT : gTermL lay i < 2 ^ 63 := by
      unfold gTermL SharedRecover.gTerm SigGolfCandidate.T3.maxDigit; split_ifs <;> omega
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
      g_spec (im := im) u upc st (gTermL lay i) _ (by omega) hT u6 u7
        (by rw [g1 _ (by simp), r12.get (by simp)]; exact h20) (by rw [g1 _ (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
      (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)) := by
      have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i st v
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [wordsOf_chainInputW_G hGb, readWords_eight]
      rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
        show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
        show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
        show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
      rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), m16]
    have hvalid : hashArgumentsValid u2 = true := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · rw [if_neg hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2) _ (fetch_49328 (im := im) u2 u2pc) h5' hvalid hq (fun a => ?_))).mono
      (by rw [chainInputW_blocks]; split_ifs <;> omega) (fun _ _ h => h)
    have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 st := by
      rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]
      exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec (im := im) (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) st hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg hm6] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i st) a) := by
      rw [gHigh_eq hGb (by omega)]
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        rw [decide_eq_false (fun h => h hm6)]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg hm6] at u212
        rw [decide_eq_true hm6]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    have fall : Frame t w StepW := fin_frame (((f02.trans hwf).trans wf).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      rw [((r02.trans rr).trans wr).get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    refine TBSim.steps (W := 0) sw (TBSim.pure ⟨wpc, w20, ?_, ?_, hval.frame wf (by decide) (by simp) (by simp),
      rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
  · -- F path: `T3.chainInput` at CHAIN
    have hGf : ClaudeWCT.WCT9.isG lay i = false := by simpa using hGb
    rw [ClaudeWCT.WCT9.chainInputW_F hGf]
    obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t2 k1 k1 u1 ∧
        expHdrK lay + k1 + trXE lay.val i st ≤ 43 ∧ u1.pc = pcOf 49331 ∧ RegsExcept t2 u1 [.x6, .x7] ∧
        Frame t2 u1 (fun _ => False) := by
      by_cases hl0 : lay.val = 0
      · rw [if_pos hl0] at p0
        have hl : lay = 0 := Fin.ext hl0
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl0]
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        by_cases hi2 : i % 2 = 0
        · rw [if_pos hi2] at p1'
          obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
            (by rw [r1'.get (by simp)]; exact g19)
          exact absurd (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl, hi2, hiT hl⟩)) hGb
        · rw [if_neg hi2] at p1'
          have hX : trXE lay.val i st = 2 := by unfold trXE; rw [if_pos (by omega)]
          exact ⟨u1, 5, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
            (f0.trans f1').mono (fun A _ h => by simp_all)⟩
      · rw [if_neg hl0] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        have hi2 : i % 2 = 0 := by
          by_contra h
          exact hGb (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨fun h' => hl0 (by rw [h']; rfl), by omega⟩))
        rw [if_pos hi2] at p1'
        have := trXE_le lay.val i st
        exact ⟨u1, 4, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
          (f0.trans f1').mono (fun A _ h => by simp_all)⟩
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
      f_spec (im := im) u1 u1pc (by rw [u1r.get (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
      (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have z0 : u2.getMem (BitVec.ofNat 64 CHAIN) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z0
    have z8 : u2.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z8
    have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
      refine hashInput_toQ u2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
        u210 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) u211 (by norm_num) ?_
      rw [readWords_eight, wordsOf_chainInput', z0, z8,
        f02.get (A := CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
        f02.get (A := CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), m16, m24, u232, u240, v2.1,
        show CHAIN + 48 + 8 = CHAIN + 56 from rfl, v2.2]
    have hvalid : hashArgumentsValid u2 = true :=
      hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by simp only [CHAIN]) (by norm_num)
        (by simp only [CHAIN]; omega) (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su1).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2 + trXE lay.val i st) _ (fetch_49336 (im := im) u2 u2pc) h5' hvalid hq
        (fun a => ?_))).mono
      (by rw [blocks_chainInput']; unfold stepW; split_ifs <;> omega) (fun _ _ h => h)
    have gw : ∀ r, r ∉ stepRegs → (writeHash u2 a).getReg r = t.getReg r := fun r hr => by
      rw [getReg_writeHash, r02.get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    have p3 : (writeHash u2 a).pc = pcOf 49337 := by rw [pc_writeHash, u2pc, pcOf_add4]
    have hlo := DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have hhi : DigAt (writeHash u2 a) (CHAIN + 64) (a.extractLsb' 128 128) :=
      DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    obtain ⟨w, s4, p4, w20, hd, r4, f4⟩ := rl1047_spec (im := im) (writeHash u2 a) p3 lay i st (by omega) (by omega)
      hGf (by rw [gw _ (by simp [stepRegs])]; exact hc.x8) (by rw [gw _ (by simp [stepRegs])]; exact hc.x19)
      (by rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]; exact h20) _ _ hlo hhi
    have fw := Frame.writeHash u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have fall : Frame t w StepW := fin_frame (((f02.trans fw).trans f4).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; omega))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), gw r hr]
    refine TBSim.steps (W := 0) s4 (TBSim.pure ⟨p4, w20, ?_, ?_, ?_, rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
    · unfold ClaudeWCT.WCT9.halfOf; exact hd

theorem chain_loop (lay : Layer) (tree leaf i d e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hd : d ≤ e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t ((e - d) * stepW lay + 1) (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) d (e - d)
    (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v Inv (stepW lay)
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step (im := im) lay tree leaf i (d + j) e hr hf (by omega) he hcap hi hiT w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)

theorem endpoint_top (i n4 : Nat) : SigGolfCandidate.T3.maxDigit 0 i = endpoint 0 i n4 := by
  simp [SigGolfCandidate.T3.maxDigit, endpoint]

theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hi : i < n) (hn : n ≤ 58)
    (hiT : lay = 0 → i ≤ 50)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (hcap : endpoint lay i n4 ≤ SigGolfCandidate.T3.maxDigit lay i)
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim im sk t 461 (ClaudeWCT.WCT9.chainW lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff lay i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW lay i W)) := by
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec (im := im) t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec (im := im) t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec (im := im) t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec (im := im) t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps im t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21, .x28] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec (im := im) t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec (im := im) ta pa i (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19)
      refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
      · simpa only [endpointExtra, if_pos hl] using qa.trans qb
      · rw [xb, he, hl, ← endpoint_top i n4]
      · exact (ra.trans rb).mono (by simp)
      · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21, .x28]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x9 := by rw [g5 _ (by simp)]; exact hc.x9
      x18 := by rw [g5 _ (by simp)]; exact hc.x18
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (im := im) (sk := sk) lay tree leaf i d e hr hf hd he7 hcap (by omega) hiT v t5 p5 hc5 x20' x21' hv5
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v =
      (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * stepW lay + 1 + 17) ≤ 461 := by
    rw [he]; unfold endpointExtra endpoint stepW SharedRecover.kmaxSteps
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 17) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1049_spec (im := im) u pu lay i (by omega) cu.x8 cu.x19
  have hslot8 : slotOff lay i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff lay i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec (im := im) u2 pu2 i (slotOff lay i) hslot8 hslot z28
    (by rw [ry2.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := fy2
  have hslotC : ∀ A, (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q2.trans q3) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by unfold slK; split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x8
        x9 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x9
        x18 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x18
        x19 := w19
        z0 := ?_, z8 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

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

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
theorem so3_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 7) ∧ t.getReg .x21 = BitVec.ofNat 64 21 ∧
      t.getReg .x20 = BitVec.ofNat 64 0 ∧ t.getReg .x25 = BitVec.ofNat 64 SEL ∧
      RegsExcept s t [.x20, .x21, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_3 hK.2.1) (codeAt_k_3 hK) s hpc (by simp [st_3, blk354_3.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_3, blk354_3.res, E.eval]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_3, blk354_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_3, blk354_3.res, rv_simp]
theorem so7_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 7)) (c : Nat)
    (hc : c ≤ 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c < 7 then pcOf (b + 9) else pcOf (b + 97)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_7 hK.2.1) (codeAt_k_7 hK) s hpc (by simp [st_7, blk354_7.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_7, rebase, blk354_7.res, E.eval, CmpOp.eval, h20]
    rw [ofNat_slt c 7 (by omega) (by omega)]
    by_cases h : c < 7 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_7, blk354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_7, blk354_7.res, rv_simp]
theorem so9_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 9))
    (c : Nat) (hc : c < 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 22 22 t ∧ t.pc = pcOf (b + 31) ∧
      t.getReg .x28 = BitVec.ofNat 64 (selWin N c) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_9 hK.2.1) (codeAt_k_9 hK) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · interval_cases c <;> simp [st_9, blk354_9.res, rv_simp, h20, accessValid_iff, MEMORY_BYTES]
  · simp [pcE_9, blk354_9.res, E.eval]
  · simp only [Result.toState_getReg, st_9, blk354_9.res]
    interval_cases c <;> simpa [rv_simp, h20] using window_mem s N hN _ hc
  · intro r hr; simp at hr; cases r <;> simp_all [st_9, blk354_9.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_9, blk354_9.res, rv_simp]
theorem so31_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if u / 16 % 128 ≤ u / 2 ^ 11 % 128 then pcOf (b + 43) else pcOf (b + 40)) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 (u / 16 % 128) ∧
      t.getReg .x23 = BitVec.ofNat 64 (u / 2 ^ 11 % 128) ∧
      t.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  have hu' : u < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_31 hK.2.1) (codeAt_k_31 hK) s hpc (by simp [st_31, blk354_31.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_31, rebase, blk354_31.res, E.eval, CmpOp.eval, h28, BinOp.eval,
      ofNat_shr _ _ hu', ofNat_and127]
    rw [ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : u / 16 % 128 ≤ u / 2 ^ 11 % 128 <;> simp [h]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · intro r hr; simp at hr; cases r <;> simp_all [st_31, blk354_31.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_31, blk354_31.res, rv_simp]
theorem so40_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 40)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 43) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_40 hK.2.1) (codeAt_k_40 hK) s hpc (by simp [st_40, blk354_40.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_40, blk354_40.res, E.eval]
  · simp [st_40, blk354_40.res, rv_simp]
  · simp [st_40, blk354_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_40, blk354_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_40, blk354_40.res, rv_simp]
theorem so43_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 43)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x24 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 47) else pcOf (b + 44)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_43 hK.2.1) (codeAt_k_43 hK) s hpc (by simp [st_43, blk354_43.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_43, rebase, blk354_43.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_43, blk354_43.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_43, blk354_43.res, rv_simp]
theorem so44_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 44)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 47) ∧ t.getReg .x23 = s.getReg .x24 ∧
      t.getReg .x24 = s.getReg .x23 ∧ RegsExcept s t [.x7, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_44 hK.2.1) (codeAt_k_44 hK) s hpc (by simp [st_44, blk354_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, blk354_44.res, E.eval]
  · simp [st_44, blk354_44.res, rv_simp]
  · simp [st_44, blk354_44.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk354_44.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_44, blk354_44.res, rv_simp]
theorem so47_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 47)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x23 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x22 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 51) else pcOf (b + 48)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_47 hK.2.1) (codeAt_k_47 hK) s hpc (by simp [st_47, blk354_47.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_47, rebase, blk354_47.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_47, blk354_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_47, blk354_47.res, rv_simp]
theorem so48_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 48)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 51) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_48 hK.2.1) (codeAt_k_48 hK) s hpc (by simp [st_48, blk354_48.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_48, blk354_48.res, E.eval]
  · simp [st_48, blk354_48.res, rv_simp]
  · simp [st_48, blk354_48.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_48, blk354_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_48, blk354_48.res, rv_simp]
theorem so51_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 51)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x22 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 52)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_51 hK.2.1) (codeAt_k_51 hK) s hpc (by simp [st_51, blk354_51.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_51, rebase, blk354_51.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_51, blk354_51.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_51, blk354_51.res, rv_simp]
theorem so52_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 52)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x23 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x24 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 53)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_52 hK.2.1) (codeAt_k_52 hK) s hpc (by simp [st_52, blk354_52.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_52, rebase, blk354_52.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_52, blk354_52.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_52, blk354_52.res, rv_simp]
theorem so53_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 53))
    (a y z R S P c : Nat) (ha : a < 256) (hy : y < 256) (hz : z < 256)
    (hP : P + 24 ≤ 2 ^ 24) (hP8 : P % 8 = 0)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 a) (h23 : s.getReg .x23 = BitVec.ofNat 64 y)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 z) (h6 : s.getReg .x6 = BitVec.ofNat 64 R)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 S) (h25 : s.getReg .x25 = BitVec.ofNat 64 P)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 44 44 t ∧ t.pc = pcOf (b + 7) ∧
      t.getReg .x21 = BitVec.ofNat 64 (S + ((a ^^^ y).log2 + 1) + ((y ^^^ z).log2 + 1) + 4) ∧
      t.getMem (BitVec.ofNat 64 P) = BitVec.ofNat 64 (R + a) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = BitVec.ofNat 64 (R + y) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = BitVec.ofNat 64 (R + z) ∧
      t.getReg .x25 = BitVec.ofNat 64 (P + 24) ∧ t.getReg .x20 = BitVec.ofNat 64 (c + 1) ∧
      RegsExcept s t [.x7, .x20, .x21, .x25, .x28, .x29] ∧
      Frame s t (fun A => A = P ∨ A = P + 8 ∨ A = P + 16) := by
  have hay : a ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) ha hy
  have hyz : y ^^^ z < 256 := Nat.xor_lt_two_pow (n := 8) hy hz
  refine ⟨_, symRun_sound (run_53 hK.2.1) (codeAt_k_53 hK) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st_53, blk354_53.res, rv_simp, h25, accessValid_iff, MEMORY_BYTES]; omega
  · simp [pcE_53, blk354_53.res, E.eval]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    simp only [rv_simp, h22, h23, h24, h21, ofNat_xor a y (by omega) (by omega),
      ofNat_xor y z (by omega) (by omega)]
    rw [bitlen_word _ hay, bitlen_word _ hyz]
    t3n []
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h22, h6]
    all_goals (split_ifs <;> first | omega | rfl)
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h23, h6]
    split_ifs <;> first | omega | rfl
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h24, h6]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h25]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_53, blk354_53.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem so97_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 97)) (S : Nat)
    (hS : S < 2 ^ 63) (h21 : s.getReg .x21 = BitVec.ofNat 64 S) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 116 ≤ S then pcOf (b + 101) else pcOf (b + 99)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_97 hK.2.1) (codeAt_k_97 hK) s hpc (by simp [st_97, blk354_97.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_97, rebase, blk354_97.res, E.eval, CmpOp.eval, h21]
    rw [ofNat_slt _ _ hS (by omega)]
    by_cases h : 116 ≤ S
    · simp [h, show ¬ S < 116 by omega]
    · simp [h, show S < 116 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_97, blk354_97.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_97, blk354_97.res, rv_simp]
theorem so99_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 99)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_99 hK.2.1) (codeAt_k_99 hK) s hpc (by simp [st_99, blk354_99.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_99, blk354_99.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_99, blk354_99.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_99, blk354_99.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_99, blk354_99.res, rv_simp]
theorem so101_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 101)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_101 hK.2.1) (codeAt_k_101 hK) s hpc (by simp [st_101, blk354_101.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_101, blk354_101.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_101, blk354_101.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_101, blk354_101.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_101, blk354_101.res, rv_simp]
end blocks
section sort
variable {image : Image} {b : Nat}
theorem exch {rlo rhi : Reg} {o nxt : Nat}
    (hsw : ∀ s : MachineState, s.pc = pcOf (b + o) → ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = s.getReg rhi ∧ t.getReg rhi = s.getReg rlo ∧ RegsExcept s t [.x7, rlo, rhi] ∧
      Frame s t (fun _ => False))
    (s : MachineState) (x y : Nat)
    (hpc : s.pc = if x ≤ y then pcOf (b + nxt) else pcOf (b + o))
    (hlo : s.getReg rlo = BitVec.ofNat 64 x) (hhi : s.getReg rhi = BitVec.ofNat 64 y) :
    ∃ k t, Steps image s k k t ∧ k ≤ 3 ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = BitVec.ofNat 64 (min x y) ∧ t.getReg rhi = BitVec.ofNat 64 (max x y) ∧
      RegsExcept s t [.x7, rlo, rhi] ∧ Frame s t (fun _ => False) := by
  by_cases h : x ≤ y
  · rw [if_pos h] at hpc
    refine ⟨0, s, Steps.refl s, by omega, hpc, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [hlo, Nat.min_eq_left h]
    · rw [hhi, Nat.max_eq_right h]
  · rw [if_neg h] at hpc
    obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := hsw s hpc
    refine ⟨3, t, h1, le_refl _, h2, ?_, ?_, h5, h6⟩
    · rw [h3, hhi, Nat.min_eq_right (by omega)]
    · rw [h4, hlo, Nat.max_eq_left (by omega)]
theorem sort_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ k t, Steps image s k k t ∧ k ≤ 20 ∧ t.pc = pcOf (b + 51) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 0 0) ∧
      t.getReg .x23 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 1 0) ∧
      t.getReg .x24 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 2 0) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, h6, h22, h23, h24, r1, f1⟩ := so31_spec hK s hpc u hu h28
  obtain ⟨k2, t2, s2, k2le, p2, a22, a23, r2, f2⟩ :=
    exch (so40_spec hK) t1 _ _ p1 h22 h23
  have b24 : t2.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) := by
    rw [r2.get (by decide), h24]
  obtain ⟨t3, s3, p3, r3, f3⟩ := so43_spec hK t2 p2 _ _ (by omega) (by omega) b24 a23
  obtain ⟨k4, t4, s4, k4le, p4, a23', a24, r4, f4⟩ :=
    exch (so44_spec hK) t3 (max (u / 16 % 128) (u / 2 ^ 11 % 128))
      (u / 2 ^ 18 % 128) p3 (by rw [r3.get (by decide), a23]) (by rw [r3.get (by decide), b24])
  have b22 : t4.getReg .x22 = BitVec.ofNat 64 (min (u / 16 % 128) (u / 2 ^ 11 % 128)) := by
    rw [r4.get (by decide), r3.get (by decide), a22]
  obtain ⟨t5, s5, p5, r5, f5⟩ := so47_spec hK t4 p4 _ _ (by omega) (by omega) a23' b22
  obtain ⟨k6, t6, s6, k6le, p6, a22', a23'', r6, f6⟩ :=
    exch (so48_spec hK) t5 _ _ p5
      (by rw [r5.get (by decide), b22]) (by rw [r5.get (by decide), a23'])
  refine ⟨9 + k2 + 1 + k4 + 1 + k6, t6, ?_, by omega, p6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
    exact this
  · rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide),
      r2.get (by decide), h6]
  · rw [a22']; rfl
  · rw [a23'']; rfl
  · rw [r6.get (by decide), r5.get (by decide), a24]; rfl
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide))
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)
end sort
def RowAt (t : MachineState) (N : BitVec 256) (c : Nat) : Prop :=
  ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
    BitVec.ofNat 64 (selBucket N c * 128 + (selRow N c).getD j 0)
def SelW (A : Nat) : Prop := SEL ≤ A ∧ A < SEL + 168
abbrev selRegs : List Reg := [.x6, .x7, .x13, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29]
theorem NAt.frame {s t : MachineState} {N : BitVec 256} (h : NAt s N) (hf : Frame s t SelW) : NAt t N := by
  intro j hj
  rw [hf.get (by simp only [NBUF]; omega) (by simp only [SelW, SEL, NBUF]; omega)]
  exact h j hj
section loop
variable {image : Image} {b : Nat}
structure SelInv (b : Nat) (s0 : MachineState) (N : BitVec 256) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 7)
  x20 : t.getReg .x20 = BitVec.ofNat 64 c
  x21 : t.getReg .x21 = BitVec.ofNat 64 (21 + selCost N c)
  x25 : t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c)
  ok : ∀ c' < c, rowOk (selRow N c') = true
  rows : ∀ c' < c, RowAt t N c'
  regs : RegsExcept s0 t selRegs
  frame : Frame s0 t SelW
macro "sel_frame" : tactic =>
  `(tactic| (intro A _ hA; (try simp only [or_false, false_or, or_self] at hA); first | exact hA | (simp only [SelW, SEL] at *; omega)))
theorem regs_mono {s t : MachineState} {l : List Reg} (h : RegsExcept s t l)
    (hl : l.all (fun r => decide (r ∈ selRegs)) = true) : RegsExcept s t selRegs :=
  h.mono (fun r hr => by simpa using List.all_eq_true.1 hl r hr)
theorem sel_body (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) {c : Nat}
    (hc : c < 7) {t : MachineState} (hI : SelInv b s0 N c t) :
    ∃ k u, Steps image t k k u ∧ k ≤ 90 ∧
      (if rowOk (selRow N c) then SelInv b s0 N (c + 1) u
       else u.pc = pcOf (b + 101) ∧ RegsExcept s0 u selRegs ∧ Frame s0 u SelW) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := so7_spec hK t hI.pc c (by omega) hI.x20
  rw [if_pos hc] at p1
  have hN1 : NAt t1 N := (hN.frame hI.frame).frame (f1.mono (by simp))
  obtain ⟨t2, s2, p2, h28, r2, f2⟩ := so9_spec hK t1 p1 c hc (by rw [r1.get (by decide), hI.x20]) N hN1
  obtain ⟨k3, t3, s3, k3le, p3, h6, h22, h23, h24, r3, f3⟩ := sort_spec hK t2 p2 _ (selWin_lt N c) h28
  have hrow : ∀ j, (selRow N c).getD j 0 < 128 := selRow_lt N c
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 ((selRow N c).getD 0 0) := h22
  have g23 : t3.getReg .x23 = BitVec.ofNat 64 ((selRow N c).getD 1 0) := h23
  have g24 : t3.getReg .x24 = BitVec.ofNat 64 ((selRow N c).getD 2 0) := h24
  obtain ⟨t4, s4, p4, r4, f4⟩ := so51_spec hK t3 p3 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) (by have := hrow 0; omega)
    (by have := hrow 1; omega) g22 g23
  have regs4 : RegsExcept s0 t4 selRegs :=
    regs_mono ((((hI.regs.trans r1).trans r2).trans r3).trans r4) (by decide)
  have frame4 : Frame s0 t4 SelW := ((((hI.frame.trans f1).trans f2).trans f3).trans f4).mono
    (by sel_frame)
  by_cases e1 : (selRow N c).getD 0 0 = (selRow N c).getD 1 0
  · rw [if_pos e1] at p4
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e1]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    refine ⟨2 + 22 + k3 + 1, t4, ((s1.trans s2).trans s3).trans s4, by omega, ?_⟩
    rw [hok]; exact ⟨p4, regs4, frame4⟩
  rw [if_neg e1] at p4
  obtain ⟨t5, s5, p5, r5, f5⟩ := so52_spec hK t4 p4 ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (by have := hrow 1; omega)
    (by have := hrow 2; omega) (by rw [r4.get (by decide), g23]) (by rw [r4.get (by decide), g24])
  by_cases e2 : (selRow N c).getD 1 0 = (selRow N c).getD 2 0
  · rw [if_pos e2] at p5
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e2]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    refine ⟨2 + 22 + k3 + 1 + 1, t5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, ?_⟩
    rw [hok]
    exact ⟨p5, regs_mono (regs4.trans r5) (by decide),
      (frame4.trans f5).mono (by sel_frame)⟩
  rw [if_neg e2] at p5
  have hok : rowOk (selRow N c) = true := by
    rw [rowOk]; simp only [ne_eq, e1, e2, not_false_eq_true, decide_true, Bool.and_self]
  have hcost := selCost_le N c
  obtain ⟨t6, s6, p6, h21', m0, m8, m16, h25', h20', r6, f6⟩ :=
    so53_spec hK t5 p5 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (selBucket N c * 128) (21 + selCost N c) (SEL + 24 * c) c (by have := hrow 0; omega) (by have := hrow 1; omega) (by have := hrow 2; omega)
      (by simp only [SEL]; omega) (by simp only [SEL]; omega)
      (by rw [r5.get (by decide), r4.get (by decide), g22])
      (by rw [r5.get (by decide), r4.get (by decide), g23])
      (by rw [r5.get (by decide), r4.get (by decide), g24])
      (by rw [r5.get (by decide), r4.get (by decide), h6]; rfl)
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x21])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x25])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x20])
  refine ⟨2 + 22 + k3 + 1 + 1 + 44, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6,
    by omega, ?_⟩
  rw [if_pos hok]
  have fr0 := (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6)
  have fr : Frame t t6 SelW := fr0.mono (by sel_frame)
  refine ⟨p6, h20', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h21', selCost_succ]; unfold rowCost; congr 1; omega
  · rw [h25']; congr 1
  · intro c' hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · exact hI.ok c' h
    · exact hok
  · intro c' hc' j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · rw [fr0.get (by simp only [SEL]; omega) (by simp only [SEL, or_false, false_or]; omega)]
      exact hI.rows c' h j hj
    · interval_cases j
      · simpa [selBucket, Nat.add_comm] using m0
      · simpa [selBucket, Nat.add_comm] using m8
      · simpa [selBucket, Nat.add_comm] using m16
  · exact regs_mono (regs4.trans (r5.trans r6)) (by decide)
  · exact (hI.frame.trans fr).mono (by intro A _ hA; rcases hA with hA | hA <;> exact hA)
theorem sel_loop (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) :
    ∀ n c t, c + n = 7 → SelInv b s0 N c t →
      ∃ k u, Steps image t k k u ∧ k ≤ 90 * n ∧
        ((u.pc = pcOf (b + 101) ∧ (List.range 7).all (fun c => rowOk (selRow N c)) = false ∧
          RegsExcept s0 u selRegs ∧ Frame s0 u SelW) ∨ SelInv b s0 N 7 u) := by
  intro n
  induction n with
  | zero => intro c t hc hI; exact ⟨0, t, Steps.refl t, le_refl _, Or.inr (by simpa using hc ▸ hI)⟩
  | succ n ih =>
    intro c t hc hI
    obtain ⟨k1, t1, s1, k1le, h1⟩ := sel_body hK hN (by omega) hI
    by_cases hok : rowOk (selRow N c) = true
    · rw [if_pos hok] at h1
      obtain ⟨k2, t2, s2, k2le, h2⟩ := ih (c + 1) t1 (by omega) h1
      exact ⟨k1 + k2, t2, s1.trans s2, by rw [Nat.mul_succ]; omega, h2⟩
    · rw [if_neg hok] at h1
      refine ⟨k1, t1, s1, by rw [Nat.mul_succ]; omega, Or.inl ⟨h1.1, ?_, h1.2⟩⟩
      rw [List.all_eq_false]
      exact ⟨c, List.mem_range.2 (by omega), hok⟩
theorem selectOk_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 640 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.admissible (T3.selections N) then 1 else 0) ∧
      (T3.admissible (T3.selections N) = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨t0, s0', p0, h21, h20, h25, r0, f0⟩ := so3_spec hK s hpc
  have hI : SelInv b s N 0 t0 :=
    ⟨p0, h20, by simpa [selCost_zero] using h21, by simpa using h25, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), regs_mono r0 (by decide), f0.mono (by intro _ _ h; exact h.elim)⟩
  obtain ⟨k1, t1, s1, k1le, h⟩ := sel_loop hK hN 7 0 t0 rfl hI
  have hx1 : ∀ u, RegsExcept s u selRegs → u.getReg .x1 = pcOf ret := fun u hu => by
    rw [hu.get (by decide), h1]
  rcases h with ⟨p1, hall, r1, f1⟩ | hI7
  · obtain ⟨t2, s2, p2, h13, r2, f2⟩ := so101_spec hK t1 p1 ret (hx1 t1 r1)
    have hadm : T3.admissible (T3.selections N) = false := by
      rw [admissible_selections, hall, Bool.false_and]
    refine ⟨4 + k1 + 2, t2, (s0'.trans s1).trans s2, by omega, p2, by rw [h13, hadm]; rfl,
      fun h => by rw [hadm] at h; exact absurd h (by decide), regs_mono (r1.trans r2) (by decide),
      f1.trans f2 |>.mono (by intro A _ hA; rcases hA with hA | hA; exact hA; exact hA.elim)⟩
  · have hS := selCost_le N 7
    obtain ⟨t2, s2, p2, r2, f2⟩ := so7_spec hK t1 hI7.pc 7 (le_refl _) hI7.x20
    rw [if_neg (by omega)] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := so97_spec hK t2 p2 (21 + selCost N 7) (by omega)
      (by rw [r2.get (by decide), hI7.x21])
    have hall : (List.range 7).all (fun c => rowOk (selRow N c)) = true :=
      List.all_eq_true.2 (fun c hc => hI7.ok c (List.mem_range.1 hc))
    have rr : RegsExcept s t3 selRegs := regs_mono ((hI7.regs.trans r2).trans r3) (by decide)
    have ff : Frame t1 t3 (fun _ => False) := (f2.trans f3).mono (by intro A _ hA; simpa using hA)
    by_cases hc : 116 ≤ 21 + selCost N 7
    · rw [if_pos hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so101_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = false := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun h => by rw [hadm] at h; exact absurd h (by decide),
        regs_mono (rr.trans r4) (by decide), ?_⟩
      exact ((hI7.frame.trans ff).trans f4).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)
    · rw [if_neg hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so99_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = true := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      have fr : Frame t1 t4 (fun _ => False) := (ff.trans f4).mono (by intro A _ hA; simpa using hA)
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun _ c hc j hj => ?_, regs_mono (rr.trans r4) (by decide),
        (hI7.frame.trans fr).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)⟩
      rw [fr.get (by simp only [SEL]; omega) (by simp)]
      exact hI7.rows c hc j hj
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gate_word (N : BitVec 256) :
    N.extractLsb' 192 64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, show (7 : Nat) = 2 ^ 3 - 1 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 3
  · simp [h, hi, show 14 + i < 64 by omega, BitVec.testBit_toNat,
      show 192 + (14 + i) = i + 206 by omega]
  · simp [h]
theorem gate_head_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if N.toNat / 2 ^ 206 % 8 = 0 then pcOf (gatePc b + 5) else pcOf (b + 101)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gate hK.2.1) (codeAt_gateHead hG) s hpc
    (by simp [gateSt, blkGateE.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    have hh : s.getMem 131448#64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
      simpa only [NBUF] using hw ▸ gate_word N
    simp only [Result.toState_pc, gateEnd, rebase, blkGateE.res, E.eval, BinOp.eval, CmpOp.eval]
    change (if (s.getMem 131448#64 >>> 14 &&& 7#64 != 0#64) = true then pcOf (b + 101) else pcOf (gatePc b + 5)) = _
    rw [hh]
    have he : (BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) = 0#64) ↔ N.toNat / 2 ^ 206 % 8 = 0 :=
      ofNat_inj (by have := Nat.mod_lt (N.toNat / 2 ^ 206) (show 0 < 8 by decide); omega) (by decide)
    simp only [bne_iff_ne, ne_eq, he, ite_not]
  · intro r hr; simp at hr; cases r <;> simp_all [gateSt, blkGateE.res, rv_simp] <;> rfl
  · intro A _ _; simp [gateSt, blkGateE.res, rv_simp]
theorem gate_jump_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 3) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gateJump hK.2.1) (codeAt_gateJump hG) s hpc
    (by simp [blkGateJE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [E.eval]
  · intro r hr; cases r <;> simp [blkGateJE.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGateJE.res, rv_simp]
theorem gatedSelect_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 646 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.digestAdmissible N then 1 else 0) ∧
      (T3.digestAdmissible N = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨u, hs, hp, hr, hf⟩ := gate_head_spec hK hG s hpc N hN
  have hN' : NAt u N := by intro j hj; rw [hf.get (by simp only [NBUF]; omega) (by simp)]; exact hN j hj
  have hu1 : u.getReg .x1 = pcOf ret := by rw [hr.get (by decide), h1]
  by_cases hg : N.toNat / 2 ^ 206 % 8 = 0
  · rw [if_pos hg] at hp
    obtain ⟨v, hs', hp', hr', hf'⟩ := gate_jump_spec hK hG u hp
    have hN'' : NAt v N := by intro j hj; rw [hf'.get (by simp only [NBUF]; omega) (by simp)]; exact hN' j hj
    have hv1 : v.getReg .x1 = pcOf ret := by rw [hr'.get (by decide), hu1]
    obtain ⟨k, t, st, hk, pt, ht13, htrows, rt, ft⟩ := selectOk_spec hK v hp' ret hv1 N hN''
    have hgB : T3.digestGate N = true := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = true; exact decide_eq_true hg
    have he : T3.digestAdmissible N = T3.admissible (T3.selections N) := by simp only [T3.digestAdmissible, hgB, Bool.and_true]
    refine ⟨5 + 1 + k, t, (hs.trans hs').trans st, by omega, pt, by simpa [he] using ht13,
      by simpa [he] using htrows, ?_, ?_⟩
    · exact regs_mono ((hr.trans hr').trans rt) (by decide)
    · exact ((hf.trans hf').trans ft).mono (by intro A _ h; simpa using h)
  · rw [if_neg hg] at hp
    obtain ⟨t, st, pt, ht13, rt, ft⟩ := so101_spec hK u hp ret hu1
    have hgB : T3.digestGate N = false := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = false; exact decide_eq_false hg
    have he : T3.digestAdmissible N = false := by simp only [T3.digestAdmissible, hgB, Bool.and_false]
    refine ⟨7, t, hs.trans st, by decide, pt, by simpa [he] using ht13,
      by simp [he], ?_, ?_⟩
    · exact regs_mono (hr.trans rt) (by decide)
    · exact (hf.trans ft).mono (by intro A _ h; simpa using h)
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) : (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    T3.pad64 (T3.digestInput rho m c) = T3.digestInput rho m c := by
  unfold T3.pad64
  rw [digestInput_length]
  simp
theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 0,
        BitVec.ofNat 64 c.toNat, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput]
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16,
    wordsOf_bytesLE32, T3.digestHeader_low, T3.digestHeader_high]
  rfl
theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]
theorem TBSim.publicHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
section blocks
variable {image : Image} {d b : Nat}
theorem ds0_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 0)) (i : Nat)
    (hi : i ≤ 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 20 then pcOf (b + 0) else pcOf (d + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds0 hD.2) (codeAt_ds_0 hD) s hpc (by simp [stds_0, blkds30_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_0, rebase, blkds30_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 20
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 1048576#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_0, blkds30_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_0, blkds30_0.res, rv_simp]
theorem ds2_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 2)) (i : Nat)
    (hi : i < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (d + 14) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 i ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run_ds2 hD.2) (codeAt_ds_2 hD) s hpc
    (by simp [stds_2, blkds30_2.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcEds_2, E.eval]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [DIG]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [h19, DIG]
    rw [Nat.mul_one]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_2, blkds30_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]
theorem ds14_fetch (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 14)) :
    fetch image s = some (.base .ECALL) :=
  ((codeAt_ds_14 hD).fetch s hpc).trans rfl
theorem ds15_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 15)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (gatePc b) ∧ t.getReg .x1 = pcOf (d + 16) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds15 hD.2) (codeAt_ds_15 hD) s hpc
    (by simp [stds_15, blkds30_15.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_15, E.eval]
  · simp [stds_15, blkds30_15.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_15, blkds30_15.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [stds_15, blkds30_15.res, rv_simp]
theorem ds16_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 16)) (ok : Bool)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if ok then pcOf (d + 19) else pcOf (d + 17)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds16 hD.2) (codeAt_ds_16 hD) s hpc
    (by simp [stds_16, blkds30_16.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_16, rebase, blkds30_16.res, E.eval, CmpOp.eval, h13]
    cases ok <;> simp
  · intro r hr; simp at hr; cases r <;> simp_all [stds_16, blkds30_16.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_16, blkds30_16.res, rv_simp]
theorem ds17_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 17)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (d + 0) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds17 hD.2) (codeAt_ds_17 hD) s hpc
    (by simp [stds_17, blkds30_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_17, E.eval]
  · simp only [Result.toState_getReg, stds_17, blkds30_17.res]
    t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_17, blkds30_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_17, blkds30_17.res, rv_simp]
end blocks
abbrev dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (d : Nat) (s : MachineState) (rho : Digest) (m : T3.Message) : Prop where
  pc : s.pc = pcOf d
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((T3.selections N).getD c ⟨0, []⟩).bucket * 128 + ((T3.selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def DsPost (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (c, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW ∧
      c.toNat < 2 ^ 20 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
def DsPostS (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCostS : Nat := T3.attemptLimit * 700 + 100
theorem selEntry_eq (N : HashOutput) (c j : Nat) (hc : c < 7) :
    selEntry N c j = selBucket N c * 128 + (selRow N c).getD j 0 := by
  simp [selEntry, selections_eq, List.getD_eq_getElem?_getD, hc]
theorem NAt.writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    NAt (writeHash t a) a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
structure DsInv (d : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (d + 0)
  hi : i ≤ 2 ^ 20
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t dsRegs
  frame : Frame s0 t DsW
theorem ds_loop (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    ∀ F i t, i + F = 2 ^ 20 → DsInv d s0 i t →
      TBSim image sk t (F * 672 + 670) (T3.digestSearch rho m i F) (DsPost b d s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, _⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := DsPost b d s0) (a := none) ⟨p2, h5, h10⟩)
    exact this.mono (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 20 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨u, s2, p2, h16, h24, h10, h11, h12, r2, f2⟩ :=
      ds2_spec hD t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u dsRegs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have u19 : u.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), r1.get (by decide), hI.x19]
    have fu : Frame s0 u DsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with h | h
      · exact h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have mem : ∀ A, A < 2 ^ 64 → ¬ DsW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ DsW A := by
      intro A hA; simp only [DsW, DIG, NBUF, SEL] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (T3.pad64 (T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput, digestInput_length]) h10 (by decide) (by decide)
        h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput, hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : T3.digestSearch rho m i (F + 1) =
        (T3.publicHash (T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if T3.digestAdmissible output then pure (some (BitVec.ofNat 32 i, output))
          else T3.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind (ds14_fetch hD u p2) h5 hv hq
      (W := 650 + (F * 672 + 670)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput]; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf (d + 15) := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : NAt (writeHash u a) a := NAt.writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    obtain ⟨t15, s15, p15, h1, r15, f15⟩ := ds15_spec hD (writeHash u a) pw
    obtain ⟨k, t16, s16, hk, p16, h13, hrows, r16, f16⟩ := gatedSelect_spec hK hD.1.2 t15 p15 (d + 16) h1 a
      (NAt.frame hN (f15.mono (fun _ _ h => h.elim)))
    obtain ⟨t17, s17, p17, r17, f17⟩ := ds16_spec hD t16 p16 _ h13
    have r17' : RegsExcept s0 t17 dsRegs :=
      ((((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans r15).trans
        r16).trans r17).mono (by decide)
    have x19' : t17.getReg .x19 = BitVec.ofNat 64 i := by
      rw [r17.get (by decide), r16.get (by decide), r15.get (by decide), getReg_writeHash, u19]
    have f17' : Frame s0 t17 DsW := ((((fu.trans fw).trans f15).trans f16).trans f17).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with (h | h) | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hN17 : NAt t17 a :=
      NAt.frame (NAt.frame (NAt.frame hN (f15.mono (fun _ _ h => h.elim))) f16) (f17.mono (fun _ _ h => h.elim))
    by_cases hadm : T3.digestAdmissible a = true
    · simp only [hadm, ↓reduceIte] at p17 ⊢
      refine (TBSim.steps (s15.trans (s16.trans s17)) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
      refine ⟨p17, by rw [r17'.get (by decide), hpre.x5], (by have hh := hadm; simp only [T3.digestAdmissible, Bool.and_eq_true] at hh; exact hh.1), hN17, ?_, r17', f17', by rw [hc]; exact hi,
        by rw [hc, x19']⟩
      intro c hc7 j hj
      rw [f17.get (by simp only [SEL]; omega) (fun h => h), hrows hadm c hc7 j hj, selEntry_eq a c j hc7]
    · have hadm' : T3.digestAdmissible a = false := by simpa using hadm
      simp only [hadm', Bool.false_eq_true, ↓reduceIte] at p17 ⊢
      obtain ⟨t18, s18, p18, h19, r18, f18⟩ := ds17_spec hD t17 p17 i x19'
      have hI' : DsInv d s0 (i + 1) t18 :=
        ⟨p18, by omega, h19, (r17'.trans r18).mono (by decide),
          (f17'.trans f18).mono (fun A _ h => by simp only [or_false] at h; exact h)⟩
      refine (TBSim.steps (s15.trans (s16.trans (s17.trans s18))) (ih (i + 1) t18 (by omega) hI')).mono
        (by omega) (fun _ _ h => h)
theorem digestSearch_tbsim (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    TBSim image sk s0 (2 ^ 20 * 672 + 670) (T3.digestSearch rho m 0 T3.attemptLimit) (DsPost b d s0) :=
  ds_loop hD hK hpre (2 ^ 20) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩
theorem digestSearch_spec (hD : DsAt image d b) (hK : KernAt image b) (s : MachineState) (rho : Digest)
    (m : T3.Message) (h : DsPre d s rho m) :
    TBSim image sk s dsCostS (T3.digestSearch rho m 0 T3.attemptLimit) (DsPostS b d s) := by
  refine (digestSearch_tbsim (sk := sk) hD hK h).mono (by unfold dsCostS T3.attemptLimit; omega)
    (fun r t ht => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1⟩
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
def PLAN : Nat := 0xff9a00
def PlanAt (t : MachineState) : Prop :=
  ∀ k < 128, t.getMem (BitVec.ofNat 64 (PLAN + 8 * k)) = bytesToWordLE ((planBytes.drop (8 * k)).take 8)
def zeroBlk : List (BitVec 32) := [28343,0x9a0eb823,0x9a0ebc23,0x9c0eb023,0x9c0eb423,2451,0xce4d606f]
def ExpandDataOK (im : Image) : Prop :=
  im.data = lplanBytes ++ planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000 in
/-- Expand joint-cost cap test `S < 790` (nested FTS joint cap 789). -/
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 41060 else pcOf 41054, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
theorem chk_cap : (optBeq (run expLook [41060, 41054] 41052 [.br true]) (resCap true) &&
    optBeq (run expLook [41060, 41054] 41052 [.br false]) (resCap false)) = true := by decide +kernel
theorem run_cap (d : Bool) : run expLook [41060, 41054] 41052 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem expCostBytes_length : expCostBytes.length = 16384 := by decide +kernel
section pieces
variable {im : Image}
theorem cap_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41052) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 789 then pcOf 41054 else pcOf 41060) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 790 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 790 < 2 ^ 64 by decide +kernel)]
    by_cases h : S < 790 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 789))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 789
    · simp only [show S < 790 by omega, if_true, h0, not_true_eq_false, decide_false]; decide +kernel
    · simp only [show ¬ S < 790 by omega, if_false, h0, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 789
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
elab "krfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let fvars := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
    let (_, g2) ← g.revert fvars (preserveOrder := true)
    g2.withContext do
      let t ← instantiateMVars (← g2.getType)
      if t.hasMVar then throwError "krfl: goal contains metavariables"
      let pf ← forallTelescope t fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "krfl: goal is not an equation"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let name ← mkAuxLemma [] t pf
      g2.assign (mkConst name)
      replaceMainGoal []
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def windowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i => expLook (n + i) == ws[i]?
theorem codeAt_of_look {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (ws : List (BitVec 32)) (hn : 0x1000 + 4 * n + 4 * ws.length < 2 ^ 64)
    (h : ∀ i, i < ws.length → look (n + i) = ws[i]?) : CodeAt im (pcOf n) ws := by
  have hpc : (pcOf n).toNat = 0x1000 + 4 * n := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ws.length
  · rw [List.getElem?_take, if_pos (by simpa using hi), List.getElem?_drop]
    have := hl (n + i) (ws[i]) (by rw [h i hi]; simp [hi])
    rw [this]; simp [hi]
  · rw [List.getElem?_eq_none (by omega)]
    by_cases hd : i < (List.drop n im.code).length
    · have := h
      rw [List.getElem?_take, if_neg (by simp; omega)]
    · rw [List.getElem?_eq_none (by simp at hd ⊢; omega)]
theorem pcOf_add_lit (n m k : Nat) (h : (0x1000 + 4 * n + k) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64) :
    pcOf n + BitVec.ofNat 64 k = pcOf m := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [← h]
  omega
theorem micro_step {im : Image} {pc : Word} {w : BitVec 32} {i : Instruction} {m : Micro}
    (hc : CodeAt im pc [w]) (hd : decodeInstruction w = some i) (hcl : classify i = some m)
    {s t : MachineState} (hpc : s.pc = pc) (he : m.exec s = some t) :
    Steps im s 1 (instructionCycles i) t := by
  have hf : fetch im s = some i := (hc.fetch s hpc).trans hd
  have := Steps.step (image := im) hf ((classify_sound hcl s).trans he) (Steps.refl t)
  simpa using this
theorem jal_x0_step {im : Image} {n m : Nat} {w : BitVec 32} {imm : BitVec 21}
    (hc : CodeAt im (pcOf n) [w]) (hd : decodeInstruction w = some (.base (.JAL .x0 imm)))
    (hoff : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcOf n) : Steps im s 1 1 (s.setPC (pcOf m)) := by
  have h := micro_step (m := .jal .x0 (signExtend21 imm)) hc hd rfl hpc (t := s.setPC (pcOf m)) (by
    simp only [Micro.exec, MachineState.setReg, hpc, Option.some.injEq]
    have e : signExtend21 imm = BitVec.ofNat 64 (signExtend21 imm).toNat := by simp
    rw [e, pcOf_add_lit n m _ hoff])
  exact h
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
theorem extractLsb'_256_toNat (a : BitVec 256) (w : Nat) :
    (a.extractLsb' (64 * w) 64).toNat = a.toNat / 2 ^ (64 * w) % 2 ^ 64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem mod_div_mod (X k m : Nat) (h : k + m ≤ 64) : X % 2 ^ 64 / 2 ^ k % 2 ^ m = X / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have : i + k < 64 := by omega
    simp [this]
  · simp [hi]
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
def base : Nat := 3164
def seg_0 : List (BitVec 32) := [16777327]
def seg_1 : List (BitVec 32) := [1049235,1049875,115]
def seg_4 : List (BitVec 32) := [100678403,125841795,52547987,19,0x5491b193]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [727827,35347219,1049491,29038483,66359,6784947,2098835,3148179,4196883,5245587,6294803,7343891,34281619,5175,0x84040413,16772663,0x600e0e13,4407,0xffc10113,20151,0x4a4e8e93,52279,0x4a4c0c13,67110291]
def seg_34 : List (BitVec 32) := [0x6003803,545171,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x60178d93,19,5789459,2586419,25626419,0x42000493,458983]
def seg_50 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x44000493,458983]
def seg_68 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x46000493,458983]
def seg_86 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x48000493,458983]
def seg_104 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x4a000493,458983]
def seg_122 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x4c000493,458983]
def seg_140 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x4e000493,458983]
def seg_158 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x50000493,458983]
def seg_176 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x52000493,458983]
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` from the forest-buffer pair 8 (`0x520`) to
`0x100` (copied to the L3 encoding block by 39142) and to the encoding R slot `0x20290`; 203 is now a NOP. -/
def seg_194 : List (BitVec 32) := [1375744387,1384134403,271593507,283128867,1392521603,1400911619,134711,675166243,686701603]
def seg_203 : List (BitVec 32) := [19]
def seg_204 : List (BitVec 32) := [0x6f92206f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (34, seg_34), (50, seg_50), (68, seg_68), (86, seg_86), (104, seg_104), (122, seg_122), (140, seg_140), (158, seg_158), (176, seg_176), (194, seg_194), (203, seg_203), (204, seg_204)]
def code : List (BitVec 32) := layoutCode layout
theorem window : windowOK base code = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
theorem child_bits (a : BitVec 256) (w sh : Nat) (h : sh + 7 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh) &&& 127#64).toNat = a.toNat / 2 ^ (64 * w + sh) % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (127#64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    mod_div_mod _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def leafO : Nat := 816
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
/-- C4: FTS node words carry the coordinate nibble `k + 1`. -/
def nodeLo (k index : Nat) : Nat := 1537 + 65536 * (k + 1) + 2 ^ 27 * index
def heapReg (h : Nat) : Reg :=
  match h with
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevel (k index j : Nat) (sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  WCT9.wctNodeHash k index (heapOf l j) pair.1 pair.2
def pairOf (j : Nat) (top sib : Digest) : Digest × Digest := if bitAt j 6 = 0 then (top, sib) else (sib, top)
def childProgC (k index j : Nat) (leaf sibs : Nat → Digest) : M (Digest × Digest) := do
  let v ← shortHash (leafBytes leaf)
  let top ← (List.range 6).foldlM (childLevel k index j sibs) v
  pure (pairOf j top (sibs 6))
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
def childWrites (j : Nat) : List Nat := stagesW j 6
/-- The 8 leaf digests (T8): `end0 | header | pad (honest 0) | end1..end5`. -/
def leafFields (k index j : Nat) (ends : List Digest) (i : Nat) : Digest :=
  if i = 0 then ends.getD 0 0 else if i = 1 then ClaudeWCT.WCT9.ftsLeafHeader index k j
  else if i = 2 then 0 else ends.getD (i - 2) 0
def sixLevels (k index j : Nat) (path : Nat → Digest) (root : Digest) : M Digest :=
  (List.range 6).foldlM (fun value l =>
    let other := path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) root
def finPath (path : Fin 7 → Digest) (l : Nat) : Digest := if h : l < 7 then path ⟨l, h⟩ else 0
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
theorem wordsOf_getD (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
def lbPc : List Nat := [48121,48127,48133,48139,48145,48151,48157,48163,48169,48175,48181,48187,48193,48199,48205,48211,48217,48223,48229,48235,48241,48247,48253,48259,48265,48271,48277,48283,48289,48295,48301,48307,48313,48319,48325,48331,48337,48343,48349,48355,48361,48367,48373,48381,48387,48393,48399,48405,48411,48417,48423,48429,48435,48441,48447,48453,48459,48465,48471,48477,48483,48489,48495,48501,48507,48513,48519,48525,48531,48537,48543,48549,48555,48561,48567,48573,48579,48585,48591,48597,48603,48609,48615,48621,48627,48633,48641,48647,48653,48659,48665,48671,48677,48683,48689,48695,48701,48707,48713,48719,48725,48731,48737,48743,48749,48755,48761,48767,48773,48779,48785,48791,48797,48803,48809,48815,48821,48827,48833,48839,48845,48851,48857,48863,48869,48875,48881,48887,48893,48901,48907,48913,48919,48925,48931,48937,48943,48949,48955,48961,48967,48973,48979,48985,48991,48997,49003,49009,49015,49021,49027,49033,49039,49045,49051,49057,49063,49069,49075,49081,49087,49093,49099,49105,49111,49117,49123,49129,49135,49141,49147,49153,49159,49165,49171,49177,49183,49189,49195,49201]
def lbS : List Nat := [22992,22856,22928,22752,22824,22648,22720,22544,22616,22440,22512,22336,22408,22232,22304,22128,22200,22024,22096,21920,21992,21816,21888,21712,21784,21608,21680,21504,21576,21400,21472,21296,21368,21192,21264,21088,21160,20984,21056,20880,20952,20776,20848,20424,20288,20360,20184,20256,20080,20152,19976,20048,19872,19944,19768,19840,19664,19736,19560,19632,19456,19528,19352,19424,19248,19320,19144,19216,19040,19112,18936,19008,18832,18904,18728,18800,18624,18696,18520,18592,18416,18488,18312,18384,18208,18280,17856,17720,17792,17616,17688,17512,17584,17408,17480,17304,17376,17200,17272,17096,17168,16992,17064,16888,16960,16784,16856,16680,16752,16576,16648,16472,16544,16368,16440,16264,16336,16160,16232,16056,16128,15952,16024,15848,15920,15744,15816,15640,15712,15208,15144,15080,15016,14952,14888,14824,14760,14696,14632,14568,14504,14440,14376,14312,14248,14184,14120,14056,13992,13928,13864,13800,13736,13672,13608,13544,13480,13416,13352,13288,13224,13160,13096,13032,12968,12904,12840,12776,12712,12648,12584,12520,12456,12392,12328,12264,12200,12136,12072,12008]
def lbX : List Nat := [0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,18446744073709551584,0,16,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,704,720,736,752,768,784]
def lbD : List Nat := [23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232]
def lbCodes : List (List (BitVec 32)) := [[25911,2634351891,340739,6664227,8729347,6665251],[25911,2491745555,340739,40218659,8729347,40219683],[25911,2567243027,340739,40220707,8729347,40221731],[25911,2382693651,340739,73773091,8729347,73774115],[25911,2458191123,340739,73775139,8729347,73776163],[25911,2273641747,340739,107327523,8729347,107328547],[25911,2349139219,340739,107329571,8729347,107330595],[25911,2164589843,340739,140881955,8729347,140882979],[25911,2240087315,340739,140884003,8729347,140885027],[21815,2055537939,340739,174436387,8729347,174437411],[21815,2131035411,340739,174438435,8729347,174439459],[21815,1946486035,340739,207990819,8729347,207991843],[21815,2021983507,340739,207992867,8729347,207993891],[21815,1837434131,340739,241545251,8729347,241546275],[21815,1912931603,340739,241547299,8729347,241548323],[21815,1728382227,340739,275099683,8729347,275100707],[21815,1803879699,340739,275101731,8729347,275102755],[21815,1619330323,340739,308654115,8729347,308655139],[21815,1694827795,340739,308656163,8729347,308657187],[21815,1510278419,340739,342208547,8729347,342209571],[21815,1585775891,340739,342210595,8729347,342211619],[21815,1401226515,340739,375762979,8729347,375764003],[21815,1476723987,340739,375765027,8729347,375766051],[21815,1292174611,340739,409317411,8729347,409318435],[21815,1367672083,340739,409319459,8729347,409320483],[21815,1183122707,340739,442871843,8729347,442872867],[21815,1258620179,340739,442873891,8729347,442874915],[21815,1074070803,340739,476426275,8729347,476427299],[21815,1149568275,340739,476428323,8729347,476429347],[21815,965018899,340739,509980707,8729347,509981731],[21815,1040516371,340739,509982755,8729347,509983779],[21815,855966995,340739,543535139,8729347,543536163],[21815,931464467,340739,543537187,8729347,543538211],[21815,746915091,340739,577089571,8729347,577090595],[21815,822412563,340739,577091619,8729347,577092643],[21815,637863187,340739,610644003,8729347,610645027],[21815,713360659,340739,610646051,8729347,610647075],[21815,528811283,340739,644198435,8729347,644199459],[21815,604308755,340739,644200483,8729347,644201507],[21815,419759379,340739,677752867,8729347,677753891],[21815,495256851,340739,677754915,8729347,677755939],[21815,310707475,340739,711307299,8729347,711308323],[21815,386204947,340739,711309347,8729347,711310371],[21815,4236576019,340739,6664227,8729347,6665251],[21815,4093969683,340739,40218659,8729347,40219683],[21815,4169467155,340739,40220707,8729347,40221731],[21815,3984917779,340739,73773091,8729347,73774115],[21815,4060415251,340739,73775139,8729347,73776163],[21815,3875865875,340739,107327523,8729347,107328547],[21815,3951363347,340739,107329571,8729347,107330595],[21815,3766813971,340739,140881955,8729347,140882979],[21815,3842311443,340739,140884003,8729347,140885027],[21815,3657762067,340739,174436387,8729347,174437411],[21815,3733259539,340739,174438435,8729347,174439459],[21815,3548710163,340739,207990819,8729347,207991843],[21815,3624207635,340739,207992867,8729347,207993891],[21815,3439658259,340739,241545251,8729347,241546275],[21815,3515155731,340739,241547299,8729347,241548323],[21815,3330606355,340739,275099683,8729347,275100707],[21815,3406103827,340739,275101731,8729347,275102755],[21815,3221554451,340739,308654115,8729347,308655139],[21815,3297051923,340739,308656163,8729347,308657187],[21815,3112502547,340739,342208547,8729347,342209571],[21815,3188000019,340739,342210595,8729347,342211619],[21815,3003450643,340739,375762979,8729347,375764003],[21815,3078948115,340739,375765027,8729347,375766051],[21815,2894398739,340739,409317411,8729347,409318435],[21815,2969896211,340739,409319459,8729347,409320483],[21815,2785346835,340739,442871843,8729347,442872867],[21815,2860844307,340739,442873891,8729347,442874915],[21815,2676294931,340739,476426275,8729347,476427299],[21815,2751792403,340739,476428323,8729347,476429347],[21815,2567243027,340739,509980707,8729347,509981731],[21815,2642740499,340739,509982755,8729347,509983779],[21815,2458191123,340739,543535139,8729347,543536163],[21815,2533688595,340739,543537187,8729347,543538211],[21815,2349139219,340739,577089571,8729347,577090595],[21815,2424636691,340739,577091619,8729347,577092643],[21815,2240087315,340739,610644003,8729347,610645027],[21815,2315584787,340739,610646051,8729347,610647075],[17719,2131035411,340739,644198435,8729347,644199459],[21815,2206532883,340739,644200483,8729347,644201507],[17719,2021983507,340739,677752867,8729347,677753891],[17719,2097480979,340739,677754915,8729347,677755939],[17719,1912931603,340739,711307299,8729347,711308323],[17719,1988429075,340739,711309347,8729347,711310371],[17719,1543832851,340739,6664227,8729347,6665251],[17719,1401226515,340739,40218659,8729347,40219683],[17719,1476723987,340739,40220707,8729347,40221731],[17719,1292174611,340739,73773091,8729347,73774115],[17719,1367672083,340739,73775139,8729347,73776163],[17719,1183122707,340739,107327523,8729347,107328547],[17719,1258620179,340739,107329571,8729347,107330595],[17719,1074070803,340739,140881955,8729347,140882979],[17719,1149568275,340739,140884003,8729347,140885027],[17719,965018899,340739,174436387,8729347,174437411],[17719,1040516371,340739,174438435,8729347,174439459],[17719,855966995,340739,207990819,8729347,207991843],[17719,931464467,340739,207992867,8729347,207993891],[17719,746915091,340739,241545251,8729347,241546275],[17719,822412563,340739,241547299,8729347,241548323],[17719,637863187,340739,275099683,8729347,275100707],[17719,713360659,340739,275101731,8729347,275102755],[17719,528811283,340739,308654115,8729347,308655139],[17719,604308755,340739,308656163,8729347,308657187],[17719,419759379,340739,342208547,8729347,342209571],[17719,495256851,340739,342210595,8729347,342211619],[17719,310707475,340739,375762979,8729347,375764003],[17719,386204947,340739,375765027,8729347,375766051],[17719,201655571,340739,409317411,8729347,409318435],[17719,277153043,340739,409319459,8729347,409320483],[17719,92603667,340739,442871843,8729347,442872867],[17719,168101139,340739,442873891,8729347,442874915],[17719,4278519059,340739,476426275,8729347,476427299],[17719,59049235,340739,476428323,8729347,476429347],[17719,4169467155,340739,509980707,8729347,509981731],[17719,4244964627,340739,509982755,8729347,509983779],[17719,4060415251,340739,543535139,8729347,543536163],[17719,4135912723,340739,543537187,8729347,543538211],[17719,3951363347,340739,577089571,8729347,577090595],[17719,4026860819,340739,577091619,8729347,577092643],[17719,3842311443,340739,610644003,8729347,610645027],[17719,3917808915,340739,610646051,8729347,610647075],[17719,3733259539,340739,644198435,8729347,644199459],[17719,3808757011,340739,644200483,8729347,644201507],[17719,3624207635,340739,677752867,8729347,677753891],[17719,3699705107,340739,677754915,8729347,677755939],[17719,3515155731,340739,711307299,8729347,711308323],[17719,3590653203,340739,711309347,8729347,711310371],[17719,3062170899,340739,4268077091,8729347,4268078115],[17719,2995062035,340739,6664227,8729347,6665251],[17719,2927953171,340739,6666275,8729347,6667299],[17719,2860844307,340739,40218659,8729347,40219683],[17719,2793735443,340739,40220707,8729347,40221731],[17719,2726626579,340739,73773091,8729347,73774115],[17719,2659517715,340739,73775139,8729347,73776163],[17719,2592408851,340739,107327523,8729347,107328547],[17719,2525299987,340739,107329571,8729347,107330595],[17719,2458191123,340739,140881955,8729347,140882979],[17719,2391082259,340739,140884003,8729347,140885027],[17719,2323973395,340739,174436387,8729347,174437411],[17719,2256864531,340739,174438435,8729347,174439459],[17719,2189755667,340739,207990819,8729347,207991843],[13623,2122646803,340739,207992867,8729347,207993891],[13623,2055537939,340739,241545251,8729347,241546275],[13623,1988429075,340739,241547299,8729347,241548323],[13623,1921320211,340739,275099683,8729347,275100707],[13623,1854211347,340739,275101731,8729347,275102755],[13623,1787102483,340739,308654115,8729347,308655139],[13623,1719993619,340739,308656163,8729347,308657187],[13623,1652884755,340739,342208547,8729347,342209571],[13623,1585775891,340739,342210595,8729347,342211619],[13623,1518667027,340739,375762979,8729347,375764003],[13623,1451558163,340739,375765027,8729347,375766051],[13623,1384449299,340739,409317411,8729347,409318435],[13623,1317340435,340739,409319459,8729347,409320483],[13623,1250231571,340739,442871843,8729347,442872867],[13623,1183122707,340739,442873891,8729347,442874915],[13623,1116013843,340739,476426275,8729347,476427299],[13623,1048904979,340739,476428323,8729347,476429347],[13623,981796115,340739,509980707,8729347,509981731],[13623,914687251,340739,509982755,8729347,509983779],[13623,847578387,340739,543535139,8729347,543536163],[13623,780469523,340739,543537187,8729347,543538211],[13623,713360659,340739,577089571,8729347,577090595],[13623,646251795,340739,577091619,8729347,577092643],[13623,579142931,340739,610644003,8729347,610645027],[13623,512034067,340739,610646051,8729347,610647075],[13623,444925203,340739,644198435,8729347,644199459],[13623,377816339,340739,644200483,8729347,644201507],[13623,310707475,340739,677752867,8729347,677753891],[13623,243598611,340739,677754915,8729347,677755939],[13623,176489747,340739,711307299,8729347,711308323],[13623,109380883,340739,711309347,8729347,711310371],[13623,42272019,340739,744861731,8729347,744862755],[13623,4270130451,340739,744863779,8729347,744864803],[13623,4203021587,340739,778416163,8729347,778417187],[13623,4135912723,340739,778418211,8729347,778419235],[13623,4068803859,340739,811970595,8729347,811971619],[13623,4001694995,340739,811972643,8729347,811973667]]
def lbHeadPc : List Nat := [48119,48379,48639,48899]
def lbHeadCodes : List (List (BitVec 32)) := [[26039,2651162003],[26039,3422913939],[26039,4194665875],[26039,688227731]]
def cTop : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593,0x00053303,0x0065b023,0x00853303,
  0x0065b423,0x01053303,0x0065b823,0x01853303,0x0065bc23]
def cClr0 : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593]
def cClrL : List (BitVec 32) := [0x00053023,0x00850513,0xfeb56ce3]
def cRet : List (BitVec 32) := [0x00003537,0xea850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe6850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe2850513,0x00053303,0x00000013,0x00853303,0x00000013,0xe8cfa06f]
def pcK (k : Nat) : Nat := lbPc.getD k 0
def sK (k : Nat) : Nat := lbS.getD k 0
def xK (k : Nat) : Nat := lbX.getD k 0
def dK (k : Nat) : Nat := lbD.getD k 0
def slotK (k : Nat) : Nat := (dK k + xK k) % 2 ^ 64
/-- Item `k` starts with a group head `li a1,D` (k = 0, 43, 86, 129). -/
def hdK (k : Nat) : Bool := k == 0 || k == 43 || k == 86 || k == 129
def grpK (k : Nat) : Nat := if k < 43 then 0 else if k < 86 then 1 else if k < 129 then 2 else 3
/-- Start pc of item `k` (its head, if any). -/
def itemPc (k : Nat) : Nat := if hdK k then pcK k - 2 else pcK k
def itemLen (k : Nat) : Nat := if hdK k then 8 else 6
theorem tab_facts : (∀ k < 180, pcK k + 6 = itemPc (k + 1) ∨ k = 179) ∧ pcK 179 + 6 = 49207 ∧ itemPc 0 = 48119 ∧
    (∀ k < 180, hdK k = true → (lbHeadPc.getD (grpK k) 0 = pcK k - 2)) ∧
    (∀ k < 180, hdK k = false → 0 < k ∧ dK k = dK (k - 1)) ∧
    (∀ k < 179, slotK k + 16 ≤ slotK (k + 1)) ∧ 23008 ≤ slotK 0 ∧ slotK 179 + 16 ≤ 26112 ∧
    (∀ k < 180, sK k % 8 = 0 ∧ sK k + 16 ≤ 23008 ∧ xK k % 8 = 0 ∧ xK k < 2 ^ 64 ∧ dK k % 8 = 0 ∧ dK k < 2 ^ 64) := by
  refine ⟨?_, by decide, by decide, ?_, ?_, ?_, by decide, by decide, ?_⟩ <;> decide
/-- The block's code. -/
structure Code (im : Image) : Prop where
  top : CodeAt im (pcOf 48100) cTop
  clr0 : CodeAt im (pcOf 48112) cClr0
  clrL : CodeAt im (pcOf 48116) cClrL
  head : ∀ g < 4, CodeAt im (pcOf (lbHeadPc.getD g 0)) (lbHeadCodes.getD g [])
  chunk : ∀ k < 180, CodeAt im (pcOf (pcK k)) (lbCodes.getD k [])
  ret : CodeAt im (pcOf 49207) cRet
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

/-- Code words of the compact/nested-FTS expansion that the paired expander keeps from the reference image. Stage 2
(C2 + C3, from #866): also the trampolines `43472 .. 43488` (`Compact2.cETail`, the footer's LE64(1) at `WIT + 24`,
and `Compact2.cRT 1..3`, the lower root windows' row-tweak pads). -/
def compactScope (n : Nat) : Bool :=
  decide ((33000≤n ∧ n<33285) ∨ (41108≤n ∧ n<42719) ∨ (43472≤n ∧ n<43489) ∨ (43951≤n ∧ n≤44043) ∨ (43500≤n ∧ n<43761))
def compactLook (n : Nat) : Option (BitVec 32) := if compactScope n then expLook n else none
namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
def cPC0 : List (BitVec 32) := [0x01500613]
def cPCL : List (BitVec 32) := [0x03053303,0x0465bc23,0x03853303,0x0665b023,0x07053303,0x0065b823,0x07853303,
  0x0065bc23,0x08050513,0x06858593,0xfff60613,0xfc061ae3]
def cPCT : List (BitVec 32) := [0x03053303,0x0265b823,0x03853303,0x0265bc23,0x00008067]
/-- The pair copy block's code (head, loop body, tail). -/
structure Code (im : Image) : Prop where
  c0 : CodeAt im (pcOf 48000) cPC0
  cL : CodeAt im (pcOf 48001) cPCL
  cT : CodeAt im (pcOf 48013) cPCT
end PairCopy
structure CompactCodeAt (im : Image) : Prop where
  look : LookOK im compactLook
  /-- Pairing stage 1: the pair copy block 48000 .. 48017. -/
  pair : PairCopy.Code im
  /-- Pairing stage 1: the leaf / digest layout block 48100 .. 49225. -/
  layout : Layout.Code im

theorem CompactCodeAt.ofNew {im : Image} (h : NewCodeAt im) (hp : PairCopy.Code im) (hl : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hp, hl⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · exact expLook_ok h n w hw
  · cases hw

def compactWindowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i=>compactLook (n+i)==ws[i]?
theorem codeAt_of_compact_window {im : Image} (hc : CompactCodeAt im) {n : Nat} {ws : List (BitVec 32)}
    (hn : 0x1000+4*n+4*ws.length<2^64) (h : compactWindowOK n ws=true) : CodeAt im (pcOf n) ws := by
  refine codeAt_of_look hc.look n ws hn (fun i hi=>?_)
  unfold compactWindowOK at h
  have:=List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
def cfgC : Config := { noAlias := true }
/-- Nested FTS (r1-1): hold slot of coordinate `k` (top sibling, flag `1 - bit6`), written by the staging pass. -/
def holdAt (k : Nat) : Nat := 0x380000 + 32 * k
def coordAt (k : Nat) : Nat := 41121 + 111 * k
def sibAt (k l : Nat) : Nat := coordAt k + 13 + 14 * l
def sibLen (l : Nat) : Nat := if l < 6 then 14 else 12
def cStart : List (BitVec 32) := [5431,0x84050513,2098615,361875,1591,0x48060613,0x7e1000ef]
def cRegs : List (BitVec 32) := [2098231,263187,5303,0x84048493,0xffa937,0xa0090913]
def cRow : List (BitVec 32) := [66712467,4428691,7932467]
def cStep : List (BitVec 32) := [0x40040413,939820179]
def cFinal : List (BitVec 32) := [13623,0xc4050513,9655,0x7c058593,1591,0x6b160613,16777455]
def cHalt : List (BitVec 32) := [62914671]
def cCopy : List (BitVec 32) := [340739,6664227,8717587,8750483,0xfff60613,0xfe0616e3,32871]
def cZero : List (BitVec 32) := [372771,8750483,0xfff60613,0xfe061ae3,32871]
def cHeads : List (List (BitVec 32)) :=[[0x6003303,217875,0x7f37993,296339,41944595,0x7cd000ef],[0x6803303,217875,0x7f37993,296339,41944595,0x611000ef],[0x6803303,22237971,0x7f37993,296339,41944595,0x455000ef],[0x6803303,59986707,0x7f37993,296339,41944595,697303279],[0x7003303,217875,0x7f37993,296339,41944595,0xdd000ef],[0x7003303,22237971,0x7f37993,296339,41944595,0x720000ef],[0x7003303,59986707,0x7f37993,296339,41944595,0x564000ef],[0x7803303,217875,0x7f37993,296339,41944595,981467375],[0x7803303,22237971,0x7f37993,296339,41944595,515899631]]
def cHead (k : Nat) : List (BitVec 32) := cHeads.getD k []
def cMids : List (List (BitVec 32)) :=[[470025491,335840659,75499027,0x7a1000ef],[470025491,335840659,75499027,0x5e5000ef],[470025491,335840659,75499027,0x429000ef],[470025491,335840659,75499027,651165935],[470025491,335840659,75499027,0xb1000ef],[470025491,335840659,75499027,0x6f4000ef],[470025491,335840659,75499027,0x538000ef],[470025491,335840659,75499027,935330031],[470025491,335840659,75499027,469762287]]
def cMid (k : Nat) : List (BitVec 32) := cMids.getD k []
/-- r3w (witness stack): the sibling blocks now differ per coordinate (store immediates `-sh k l`), index `6 k + l`. -/
def cSibs : List (List (BitVec 32)) :=[[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,31338531,32388131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4259199011,4260248611],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4259199011,4260248611],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4259199011,4260248611],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4259199011,4260248611],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4259199011,4260248611],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4259199011,4260248611],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4225642531,4226692131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4225642531,4226692131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4225642531,4226692131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4225642531,4226692131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4225642531,4226692131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4225642531,4226692131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4158535715,4159585315],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4158535715,4159585315],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4158535715,4159585315],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4158535715,4159585315],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4158535715,4159585315],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4158535715,4159585315],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4124979235,4126028835],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4124979235,4126028835],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4124979235,4126028835],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4124979235,4126028835],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4124979235,4126028835],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4124979235,4126028835],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4057872419,4058922019],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4057872419,4058922019],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4057872419,4058922019],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4057872419,4058922019],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4057872419,4058922019],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4057872419,4058922019],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4024315939,4025365539],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4024315939,4025365539],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4024315939,4025365539],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4024315939,4025365539],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4024315939,4025365539],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4024315939,4025365539],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3957209123,3958258723],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,3957209123,3958258723],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,3957209123,3958258723],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,3957209123,3958258723],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,3957209123,3958258723],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,3957209123,3958258723],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3923652643,3924702243]]
def cSib (k l : Nat) : List (BitVec 32) := cSibs.getD (6 * k + l) []
section code
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cStart : CodeAt im (pcOf 41108) cStart := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRegs : CodeAt im (pcOf 41115) cRegs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cFinal : CodeAt im (pcOf 42120) cFinal := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHalt : CodeAt im (pcOf 42127) cHalt := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCopy : CodeAt im (pcOf 42130) cCopy := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero : CodeAt im (pcOf 42137) cZero := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_copyRet : CodeAt im (pcOf 42136) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_zeroRet : CodeAt im (pcOf 42141) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHead (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k)) (cHead k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cMid (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 6)) (cMid k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 10)) cRow := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cStep (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 109)) cStep := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
/-- Nested FTS (r1-1): levels 0..5 run in place (level 5 now writes to the fixed staging block at +832); level 6
jumps to a per-coordinate trampoline (`sib6_spec`). -/
theorem code_cSib (k l : Nat) (hk : k < 9) (hl : l < 6) : CodeAt im (pcOf (sibAt k l)) (cSib k l) := by
  interval_cases k <;> interval_cases l <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
sym_block RStart := symRun cfgC cStart (pcOf 41108) 40
sym_block RRegs := symRun cfgC cRegs (pcOf 41115) 40
sym_block RFinal := symRun cfgC cFinal (pcOf 42120) 40
sym_block RHalt := symRun cfgC cHalt (pcOf 42127) 40
sym_block RCopy := symRun cfgC cCopy (pcOf 42130) 40
sym_block RCopyRet := symRun cfgC [0x8067] (pcOf 42136) 40
sym_block RZero := symRun cfgC cZero (pcOf 42137) 40
sym_block RZeroRet := symRun cfgC [0x8067] (pcOf 42141) 40
sym_block RHead0 := symRun cfgC (cHead 0) (pcOf (coordAt 0)) 40
sym_block RMid0 := symRun cfgC (cMid 0) (pcOf (coordAt 0 + 6)) 40
sym_block RHead1 := symRun cfgC (cHead 1) (pcOf (coordAt 1)) 40
sym_block RMid1 := symRun cfgC (cMid 1) (pcOf (coordAt 1 + 6)) 40
sym_block RHead2 := symRun cfgC (cHead 2) (pcOf (coordAt 2)) 40
sym_block RMid2 := symRun cfgC (cMid 2) (pcOf (coordAt 2 + 6)) 40
sym_block RHead3 := symRun cfgC (cHead 3) (pcOf (coordAt 3)) 40
sym_block RMid3 := symRun cfgC (cMid 3) (pcOf (coordAt 3 + 6)) 40
sym_block RHead4 := symRun cfgC (cHead 4) (pcOf (coordAt 4)) 40
sym_block RMid4 := symRun cfgC (cMid 4) (pcOf (coordAt 4 + 6)) 40
sym_block RHead5 := symRun cfgC (cHead 5) (pcOf (coordAt 5)) 40
sym_block RMid5 := symRun cfgC (cMid 5) (pcOf (coordAt 5 + 6)) 40
sym_block RHead6 := symRun cfgC (cHead 6) (pcOf (coordAt 6)) 40
sym_block RMid6 := symRun cfgC (cMid 6) (pcOf (coordAt 6 + 6)) 40
sym_block RHead7 := symRun cfgC (cHead 7) (pcOf (coordAt 7)) 40
sym_block RMid7 := symRun cfgC (cMid 7) (pcOf (coordAt 7 + 6)) 40
sym_block RHead8 := symRun cfgC (cHead 8) (pcOf (coordAt 8)) 40
sym_block RMid8 := symRun cfgC (cMid 8) (pcOf (coordAt 8 + 6)) 40
sym_block RRow := symRun cfgC cRow (pcOf (coordAt 0 + 10)) 40
sym_block RStep := symRun cfgC cStep (pcOf (coordAt 0 + 109)) 40
theorem run_row (k : Nat) (hk : k < 9) : symRun cfgC cRow (pcOf (coordAt k + 10)) 40 =
    some ⟨RRow.res.st, .c (pcOf (coordAt k + 13)), .endOfCode, 3, 3⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_step (k : Nat) (hk : k < 9) : symRun cfgC cStep (pcOf (coordAt k + 109)) 40 =
    some ⟨RStep.res.st, .c (pcOf (coordAt k + 111)), .endOfCode, 2, 2⟩ := by
  interval_cases k <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def compactChunkAllowed (c : Nat) : Prop :=
  c=128 ∨ c=129 ∨ c=130 ∨ (160≤c ∧ c≤166) ∨ c=169 ∨ c=170 ∨ c=171 ∨ c=172
/-- Window `[compactChunkLo c, compactChunkLen c)` of image chunk `c` used by `compactScope` (chunk 169 only for the
stage-2 trampolines and C4 prefix; chunk 170 stops before the paired suffix jump at 43761). -/
def compactChunkLo (c : Nat) : Nat := if c=169 then 208 else 0
def compactChunkLen (c : Nat) : Nat := if c=172 then 12 else if c=170 then 241 else 256
theorem compactCode_of_chunks {im : Image}
    (hc : ∀c,compactChunkAllowed c → CodeAt im (pcOf (256*c+compactChunkLo c))
      (((expChunks.getD (c-4) []).take (compactChunkLen c)).drop (compactChunkLo c)))
    (hpair : PairCopy.Code im) (hlay : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hpair, hlay⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · rename_i hs
    have hn := of_decide_eq_true hs
    have ha : compactChunkAllowed (n/256) := by unfold compactChunkAllowed; omega
    have hlo : compactChunkLo (n/256) ≤ n%256 := by unfold compactChunkLo; split <;> omega
    have hlo' : compactChunkLo (n/256) < 256 := by unfold compactChunkLo; split <;> omega
    have hl : n%256<compactChunkLen (n/256) := by unfold compactChunkLen; split_ifs <;> omega
    have hp : 1024≤n := by omega
    unfold expLook at hw
    rw [if_pos hp] at hw
    have ht : (((expChunks.getD (n/256-4) []).take (compactChunkLen (n/256))).drop
        (compactChunkLo (n/256)))[n%256-compactChunkLo (n/256)]?=some w := by
      rw [List.getElem?_drop,show compactChunkLo (n/256)+(n%256-compactChunkLo (n/256))=n%256 by omega,
        List.getElem?_take,if_pos hl]
      exact hw
    have hb : (pcOf (256*(n/256)+compactChunkLo (n/256))).toNat=0x1000+4*(256*(n/256)+compactChunkLo (n/256)) := by
      rw [pcOf,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; omega
    obtain ⟨_,_,_,hpre⟩ := hc (n/256) ha
    rw [hb] at hpre
    obtain ⟨rest,hrest⟩ := hpre
    have hh := congrArg (·[n%256-compactChunkLo (n/256)]?) hrest
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1,ht,List.getElem?_drop] at hh
    rw [show (0x1000+4*(256*(n/256)+compactChunkLo (n/256))-0x1000)/4+(n%256-compactChunkLo (n/256))=n by omega] at hh
    exact hh.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cSnap : List (BitVec 32) := [5431,2147812627,3212727,361875,5687,2861958675,4221563119]
def cZero2 : List (BitVec 32) := [1463,1208321427,5687,3276146195,4229951727]  -- nested FTS: zero 2718 words from 1216
/-- Nested FTS (r1-1): the header copy is replaced by `jal zero,P_final` (P_final at words 33117..33284). -/
def cHdr : List (BitVec 32) := [2899275887]
def cCtr : List (BitVec 32) := [3212599,33883411,1241515411,2098707,1280344303]
def cPRegs : List (List (BitVec 32)) := [[3212599,67437843,9655,2055570835,117442067,1255178479],[3212599,1006961939,9655,1116046739,117442067,1230012655],[3212599,1946486035,9655,176522643,117442067,1204846831],[3216695,2886010131,9655,3531965843,117442067,1179681007],[3216695,3825534227,9655,2592441747,117442067,1154515183],[3216695,470091027,5559,1652917651,117442067,1129349359],[3216695,1409615123,5559,713393555,117442067,1104183535],[3220791,2349139219,5559,4068836755,117442067,1079017711],[3220791,3288663315,5559,3129312659,117442067,1053851887]]
def cHolds : List (List (BitVec 32)) := [[3673655,17710979,933507,9322243,8361619,5218195,32933555,9015,201523987,6719155,4023824419,4024874019],[3673655,51265411,34487939,42876675,8361619,5218195,32933555,9015,3556967187,6719155,4057380899,4058430499],[3673655,84819843,68042371,76431107,8361619,5218195,32933555,9015,2617443091,6719155,4124487715,4125537315],[3673655,118374275,101596803,109985539,8361619,5218195,32933555,4919,1677918995,6719155,4158044195,4159093795],[3673655,151928707,135151235,143539971,8361619,5218195,32933555,4919,738394899,6719155,4225151011,4226200611],[3673655,185483139,168705667,177094403,8361619,5218195,32933555,4919,4093838099,6719155,4258707491,4259757091],[3673655,219037571,202260099,210648835,8361619,5218195,32933555,4919,3154314003,6719155,30847011,31896611],[3673655,252592003,235814531,244203267,8361619,5218195,32933555,4919,2214789907,6719155,30847011,31896611],[3673655,286146435,269368963,277757699,8361619,5218195,32933555,823,1275265811,6719155,30847011,31896611]]
def cPEnd : List (BitVec 32) := [990937199]
def cPReg (c : Nat) : List (BitVec 32) := cPRegs.getD c []
def cHold (c : Nat) : List (BitVec 32) := cHolds.getD c []
def pregAt (c : Nat) : Nat := 33122 + 6 * c
def holdPc (c : Nat) : Nat := 33176 + 12 * c
def cTop : List (BitVec 32) := [3220791,4236576019,13751,2944763283,1591,554042899,3877630191]
def cIdx : List (BitVec 32) := [0x6003b03,35347219,0xff9937,0x40090913]
def cCh1 : List (BitVec 32) := [3224887,545588499,17847,3498411411,1591,361104915,533745903]
def cRow1 : List (BitVec 32) := [0xcb5993,0x7f9f993,3774995,19532339,537528851]
def cLv10 : List (BitVec 32) := [3224887,478479635,672515,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv11 : List (BitVec 32) := [3224887,411370771,1721091,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv12 : List (BitVec 32) := [3224887,344261907,2769667,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv13 : List (BitVec 32) := [3224887,277153043,3818243,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv14 : List (BitVec 32) := [3224887,210044179,4866819,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv15 : List (BitVec 32) := [3224887,142935315,5915395,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv16 : List (BitVec 32) := [3224887,75826451,6963971,4395795,17847,3078981011,6653363,33898115,42286851,64335907,243273839,6935315,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh2 : List (BitVec 32) := [3228983,3833922835,17847,1896187283,1591,361104915,1954566383]
def cRow2 : List (BitVec 32) := [7035283,66714003,3774995,19532339]
def cLv20 : List (BitVec 32) := [3228983,3766813971,672515,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv21 : List (BitVec 32) := [3228983,3699705107,1721091,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv22 : List (BitVec 32) := [3228983,3632596243,2769667,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv23 : List (BitVec 32) := [3228983,3565487379,3818243,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv24 : List (BitVec 32) := [3228983,3498378515,4866819,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv25 : List (BitVec 32) := [3228983,3431269651,5915395,4395795,17847,1560642963,6653363,33898115,42286851,64335907,1783627887,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh3 : List (BitVec 32) := [3233079,2827289875,21943,293963155,1591,361104915,1329615087]
def cRow3 : List (BitVec 32) := [66812307,3774995,19532339]
def cLv30 : List (BitVec 32) := [3233079,2760181011,672515,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv31 : List (BitVec 32) := [3233079,2693072147,1721091,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv32 : List (BitVec 32) := [3233079,2625963283,2769667,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv33 : List (BitVec 32) := [3233079,2558854419,3818243,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv34 : List (BitVec 32) := [3233079,2491745555,4866819,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv35 : List (BitVec 32) := [3233079,2424636691,5915395,4395795,21943,4253386131,6653363,33898115,42286851,64335907,1179648111,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cTail : List (BitVec 32) := [3212599,328979,26039,2651162003,343683,8732419,30781475,31831075,17133187,374819,30784547]
def lvAt (lay j : Nat) : Nat := if lay = 1 then 42247 + 23 * j else if lay = 2 then 42419 + 23 * j else 42567 + 23 * j
def cLvs : List (List (BitVec 32)) := [cLv10, cLv11, cLv12, cLv13, cLv14, cLv15, cLv16, cLv20, cLv21, cLv22, cLv23, cLv24, cLv25, cLv30, cLv31, cLv32, cLv33, cLv34, cLv35]
def lvIdx (lay j : Nat) : Nat := if lay = 1 then j else if lay = 2 then 7 + j else 13 + j
def cLv (lay j : Nat) : List (BitVec 32) := cLvs.getD (lvIdx lay j) []
/-- C3 (FULL, E6): the root level of each lower layer jumps after its Z-pad copy to a trampoline that writes LE64(1)
at window + 24 (the encoding row tweak's high word, honest 1) and returns. -/
def rtAt (lay : Nat) : Nat := if lay = 1 then 43477 else if lay = 2 then 43481 else 43485
def cRT (lay : Nat) : List (BitVec 32) :=
  if lay = 1 then [65385507,1052307,30784547,4045398127] else if lay = 2 then [65385507,1052307,30784547,2505044079]
  else [65385507,1052307,30784547,3109023855]
def rootJ (lay : Nat) : Nat := if lay = 1 then 6 else 5
def cLvA (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).take 11
def cLvB (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).drop 11
section code
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
theorem code_cSnap : CodeAt im (pcOf 42142) cSnap := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero2 : CodeAt im (pcOf 42149) cZero2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHdr : CodeAt im (pcOf 42154) cHdr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTop : CodeAt im (pcOf 42224) cTop := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCtr : CodeAt im (pcOf 33117) cCtr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPEnd : CodeAt im (pcOf 33284) cPEnd := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPReg (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (pregAt c)) (cPReg c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHold (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (holdPc c)) (cHold c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cIdx : CodeAt im (pcOf 42231) cIdx := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh1 : CodeAt im (pcOf 42235) cCh1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow1 : CodeAt im (pcOf 42242) cRow1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh2 : CodeAt im (pcOf 42408) cCh2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow2 : CodeAt im (pcOf 42415) cRow2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh3 : CodeAt im (pcOf 42557) cCh3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow3 : CodeAt im (pcOf 42564) cRow3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTail : CodeAt im (pcOf 42705) cTail := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < (if lay = 1 then 7 else 6)) :
    CodeAt im (pcOf (lvAt lay j)) (cLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (lvAt lay (rootJ lay))) (cLvA lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    CodeAt im (pcOf (lvAt lay (rootJ lay) + 11)) (cLvB lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRT (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (rtAt lay)) (cRT lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
sym_block RIdx := symRun cfgC cIdx (pcOf 42231) 40
sym_block RRow1 := symRun cfgC cRow1 (pcOf 42242) 40
sym_block RRow2 := symRun cfgC cRow2 (pcOf 42415) 40
sym_block RRow3 := symRun cfgC cRow3 (pcOf 42564) 40
sym_block RTail := symRun cfgC cTail (pcOf 42705) 40
sym_block RLv10 := symRun cfgC (cLv 1 0) (pcOf (lvAt 1 0)) 40
sym_block RLv11 := symRun cfgC (cLv 1 1) (pcOf (lvAt 1 1)) 40
sym_block RLv12 := symRun cfgC (cLv 1 2) (pcOf (lvAt 1 2)) 40
sym_block RLv13 := symRun cfgC (cLv 1 3) (pcOf (lvAt 1 3)) 40
sym_block RLv14 := symRun cfgC (cLv 1 4) (pcOf (lvAt 1 4)) 40
sym_block RLv15 := symRun cfgC (cLv 1 5) (pcOf (lvAt 1 5)) 40
sym_block RLv16 := symRun cfgC (cLv 1 6) (pcOf (lvAt 1 6)) 40
sym_block RLv20 := symRun cfgC (cLv 2 0) (pcOf (lvAt 2 0)) 40
sym_block RLv21 := symRun cfgC (cLv 2 1) (pcOf (lvAt 2 1)) 40
sym_block RLv22 := symRun cfgC (cLv 2 2) (pcOf (lvAt 2 2)) 40
sym_block RLv23 := symRun cfgC (cLv 2 3) (pcOf (lvAt 2 3)) 40
sym_block RLv24 := symRun cfgC (cLv 2 4) (pcOf (lvAt 2 4)) 40
sym_block RLv25 := symRun cfgC (cLv 2 5) (pcOf (lvAt 2 5)) 40
sym_block RLv30 := symRun cfgC (cLv 3 0) (pcOf (lvAt 3 0)) 40
sym_block RLv31 := symRun cfgC (cLv 3 1) (pcOf (lvAt 3 1)) 40
sym_block RLv32 := symRun cfgC (cLv 3 2) (pcOf (lvAt 3 2)) 40
sym_block RLv33 := symRun cfgC (cLv 3 3) (pcOf (lvAt 3 3)) 40
sym_block RLv34 := symRun cfgC (cLv 3 4) (pcOf (lvAt 3 4)) 40
sym_block RLv35 := symRun cfgC (cLv 3 5) (pcOf (lvAt 3 5)) 40
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def nbE (j : Nat) : E := .bin .xor (.bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 j))) (.c 1#64)) (.c 1#64)
def t6E (j : Nat) : E := .bin .add (.bin .sll (nbE j) (.c 4#64)) (.bin .sll (nbE j) (.c 5#64))
def pbE (j : Nat) : E := .un (.ld .bu j) (E.ld (.reg .x20))
def slotE (j : Nat) : E := .bin .sll (pbE j) (.c 4#64)
def a0E (j S : Nat) : E := .bin .add (t6E j) (.c (BitVec.ofNat 64 S))
def a1E (j D : Nat) : E := .bin .add (.bin .add (slotE j) (.c (BitVec.ofNat 64 D))) (t6E j)
def lvRegs (j S D : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (a0E j S)).set .x11
    (a1E j D)).set .x29 (a0E j S).ld).set .x30 (a0E j (S + 8)).ld
def lvMem (j S D : Nat) : SymMem :=
  [(⟨some (a1E j D), 8#64⟩, (a0E j (S + 8)).ld), (⟨some (a1E j D), 0#64⟩, (a0E j S).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩, (E.c (BitVec.ofNat 64 (S + 40))).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvObl (j S D : Nat) : List Oblig :=
  [.valid ⟨some (a1E j D), 8#64⟩ 8, .valid ⟨some (a1E j D), 0#64⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 S⟩ 8,
   .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩ 8, .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8,
   .align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def lvSrc (lay j : Nat) : Nat :=
  0x310000 + 8136 + 64 * ((if lay = 1 then 66 else if lay = 2 then 116 else 165) + (if lay = 1 then 6 else 5) - j)
/-- Lower-layer path area in the final witness (pairing stage 1: abs `2904 + layerBase` = 15224 / 17872 / 20440). -/
def lvDst (lay : Nat) : Nat := 0x800 + (if lay = 1 then 13176 else if lay = 2 then 15824 else 18392)
def lvH (lay : Nat) : Nat := if lay = 1 then 7 else 6
def rLvs : List Result := [RLv10.res, RLv11.res, RLv12.res, RLv13.res, RLv14.res, RLv15.res, RLv16.res, RLv20.res,
  RLv21.res, RLv22.res, RLv23.res, RLv24.res, RLv25.res, RLv30.res, RLv31.res, RLv32.res, RLv33.res, RLv34.res,
  RLv35.res]
def rLv (lay j : Nat) : Result := rLvs.getD (lvIdx lay j) RLv10.res
theorem rLv_eq (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    rLv lay j = ⟨⟨lvRegs j (lvSrc lay j) (lvDst lay), lvMem j (lvSrc lay j) (lvDst lay),
      lvObl j (lvSrc lay j) (lvDst lay)⟩, .c (pcOf (lvAt lay j + 23)), .endOfCode, 23, 23⟩ := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
theorem run_lv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    symRun cfgC (cLv lay j) (pcOf (lvAt lay j)) 40 = some (rLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
def LPLAN : Nat := 0xff9400
def LPlanAt (t : MachineState) : Prop :=
  ∀ k < 192, t.getMem (BitVec.ofNat 64 (LPLAN + 8 * k)) = bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * k)).take 8)
/-! ### C4: the top-path plan table of the expander's post-pass (data offset 26496 = legacy offset 2944) -/
/-- Line-A table (row `leaf % 64`, the six sibling slots of levels 0..5, stride 8) at `0xfffb80`. -/
def TOPA : Nat := 0xfffb80
/-- Line-B table (row `leaf / 64`, the six sibling slots of levels 6..11) at `0xfffd80`. -/
def TOPB : Nat := 0xfffd80
def topABytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 2944).take 512
def topBBytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 3456).take 512
def TopTabAt (t : MachineState) : Prop :=
  (∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPA + 8 * k)) = bytesToWordLE ((topABytes.drop (8 * k)).take 8)) ∧
  ∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPB + 8 * k)) = bytesToWordLE ((topBBytes.drop (8 * k)).take 8)
/-- Sibling slot (16-byte unit of the 48-slot top path area) of level `jj` in row `r` of line A (levels 0..5). -/
def slotA (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanA.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
/-- Sibling slot of level `jj + 6` in row `r` of line B. -/
def slotB (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanB.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
set_option maxRecDepth 100000 in
theorem topA_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topABytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotA r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem topB_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topBBytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotB r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
/-- Line A's sibling slots lie in `[24, 47]`, line B's in `[0, 23]`; within a line they are pairwise distinct. -/
theorem slots_ok : (∀ r < 64, ∀ i < 6, 24 ≤ slotA r i ∧ slotA r i ≤ 47) ∧ (∀ r < 64, ∀ i < 6, slotB r i ≤ 23) ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotA r i = slotA r i' → i = i') ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotB r i = slotB r i' → i = i') := by
  decide +kernel
def lvRow (lay r : Nat) : Nat := if lay = 1 then 64 + r else r
set_option maxRecDepth 100000 in
theorem lplan1_ok : ∀ r < 128, ∀ j < 7,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * (64 + r))).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lplan2_ok : ∀ r < 64, ∀ j < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * r)).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0) ∧
    (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 3 r).getD j 0 = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lowerPlan_lt : (∀ r < 128, ∀ j < 7, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0 + 4 ≤ 25) ∧
    (∀ r < 64, ∀ j < 6, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 + 4 ≤ 20) := by
  decide +kernel
def plan (lay r j : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan (Fin.ofNat 4 lay) r).getD j 0
theorem plan_ok (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * lvRow lay r)).take 8)) j =
      BitVec.ofNat 64 (plan lay r j) ∧ plan lay r j + 4 ≤ (if lay = 1 then 25 else 20) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hr hj
  unfold plan lvRow
  interval_cases lay
  · simp only [if_true] at hr hj ⊢
    exact ⟨lplan1_ok r (by omega) j hj, lowerPlan_lt.1 r (by omega) j hj⟩
  · simp only [show (2 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
  · simp only [show (3 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    rw [show (Fin.ofNat 4 3 : SigGolfCandidate.T3.Layer) = 3 from rfl, (lplan2_ok r (by omega) j hj).2]
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
theorem nbE_eval (j : Nat) (hj : j < 7) : (nbE j).eval s = BitVec.ofNat 64 (1 - r / 2 ^ j % 2) := by
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  apply BitVec.eq_of_toNat_eq
  simp only [nbE, E.eval, BinOp.eval, h19, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  rcases (show r / 2 ^ j % 2 = 0 ∨ r / 2 ^ j % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (j : Nat) (hj : j < 7) : (t6E j).eval s = BitVec.ofNat 64 (48 * (1 - r / 2 ^ j % 2)) := by
  have hb := nbE_eval h19 hr j hj
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show r / 2 ^ j % 2 = 0 ∨ r / 2 ^ j % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
end eval
theorem pbE_eval {s : MachineState} {lay r : Nat} (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) (j : Nat) (hj : j < lvH lay) :
    (pbE j).eval s = BitVec.ofNat 64 (plan lay r j) := by
  have hrow : lvRow lay r < 192 := by
    unfold lvRow lvH at *; split <;> simp_all <;> omega
  simp only [pbE, E.eval, UnOp.eval, h20]
  rw [hp _ hrow, (plan_ok lay r j hl hr hj).1]
theorem lvH_le (lay : Nat) : lvH lay ≤ 7 := by unfold lvH; split <;> omega
theorem valid8 (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lv_spec (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj' : j + 1 < lvH lay) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay j)) (r : Nat) (hr : r < 2 ^ lvH lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 23 23 t ∧ t.pc = pcOf (lvAt lay j + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2)))
        else if A = lvDst lay + 16 * plan lay r j + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 40))
        else if A = lvDst lay + 16 * plan lay r j + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hj : j < lvH lay := by omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : j < 7 := by omega
  have ht6 := t6E_eval h19 hr7 j hj7
  have hpb := pbE_eval hl hr h20 hp j hj
  have hpl := (plan_ok lay r j hl hr hj).2
  have hpl23 : plan lay r j ≤ 23 := by split_ifs at hpl <;> omega
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hD : lvDst lay + 16 * 23 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst; split_ifs <;> omega
  have hDp : lvDst lay + 16 * plan lay r j + 64 ≤ 0x800 + 20912 := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
  have hS16 : lvSrc lay j % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  have hrun := run_lv lay j ⟨h1, h4⟩ (by omega)
  rw [rLv_eq lay j ⟨h1, h4⟩ (by omega)] at hrun
  have hslot : (slotE j).eval s = BitVec.ofNat 64 (16 * plan lay r j) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  have ha0 : ∀ S, (a0E j S).eval s = BitVec.ofNat 64 (48 * (1 - r / 2 ^ j % 2) + S) := fun S => by
    simp only [a0E, E.eval, BinOp.eval, ht6, ofNat_add_ofNat]
  have ha1 : (a1E j (lvDst lay)).eval s =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)) := by
    simp only [a1E, E.eval, BinOp.eval, hslot, ht6, ofNat_add_ofNat]; congr 1; ring
  have hobl : Oblig.all s (lvObl j (lvSrc lay j) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  refine ⟨_, symRun_sound hrun (Compact2.code_cLv hc lay j ⟨h1, h4⟩ hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    simp only [Result.toState_getMem, lvMem, memEval_cons, memEval_nil, Addr.eval, E.eval, ha0, ha1, hslot,
      ofNat_add_ofNat, BitVec.add_zero]
    have e1 : 48 * (1 - r / 2 ^ j % 2) + (lvSrc lay j + 8) = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8 := by ring
    have e2 : 48 * (1 - r / 2 ^ j % 2) + lvSrc lay j = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) := by ring
    have e3 : 16 * plan lay r j + (lvDst lay + 40) = lvDst lay + 16 * plan lay r j + 40 := by ring
    have e4 : 16 * plan lay r j + (lvDst lay + 32) = lvDst lay + 16 * plan lay r j + 32 := by ring
    rw [e1, e2, e3, e4]
    by_cases q1 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8
    · subst q1; simp
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h)), if_neg q1]
      by_cases q2 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)
      · subst q2; simp
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
        by_cases q3 : A = lvDst lay + 16 * plan lay r j + 40
        · subst q3; simp
        · rw [if_neg (fun h => q3 ((ofNat_inj hA (by omega)).mp h)), if_neg q3]
          by_cases q4 : A = lvDst lay + 16 * plan lay r j + 32
          · subst q4; simp
          · rw [if_neg (fun h => q4 ((ofNat_inj hA (by omega)).mp h)), if_neg q4]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
sym_block RLvA1 := symRun cfgC (cLvA 1) (pcOf (lvAt 1 (rootJ 1))) 40
sym_block RLvA2 := symRun cfgC (cLvA 2) (pcOf (lvAt 2 (rootJ 2))) 40
sym_block RLvA3 := symRun cfgC (cLvA 3) (pcOf (lvAt 3 (rootJ 3))) 40
sym_block RRT1 := symRun cfgC (cRT 1) (pcOf (rtAt 1)) 40
sym_block RRT2 := symRun cfgC (cRT 2) (pcOf (rtAt 2)) 40
sym_block RRT3 := symRun cfgC (cRT 3) (pcOf (rtAt 3)) 40
sym_block RLvB1 := symRun cfgC (cLvB 1) (pcOf (lvAt 1 (rootJ 1) + 11)) 40
sym_block RLvB2 := symRun cfgC (cLvB 2) (pcOf (lvAt 2 (rootJ 2) + 11)) 40
sym_block RLvB3 := symRun cfgC (cLvB 3) (pcOf (lvAt 3 (rootJ 3) + 11)) 40
def lvARegs (j S D : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (slotE j)).set .x10 (.c (BitVec.ofNat 64 S))).set .x11
    (.bin .add (slotE j) (.c (BitVec.ofNat 64 D)))).set .x29 (E.c (BitVec.ofNat 64 (S + 32))).ld).set .x30
    (E.c (BitVec.ofNat 64 (S + 40))).ld
def lvAMem (j S D : Nat) : SymMem :=
  [(⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvAObl (j D : Nat) : List Oblig :=
  [.valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8, .align8 (.reg .x20),
   .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def rtRegs : RegFile := RegFile.init.set .x29 (.c 1#64)
def rtMem : SymMem := [(⟨some (.reg .x11), 24#64⟩, .c 1#64), (⟨some (.reg .x11), 40#64⟩, .reg .x30)]
def rtObl : List Oblig := [.valid ⟨some (.reg .x11), 24#64⟩ 8, .valid ⟨some (.reg .x11), 40#64⟩ 8]
def aBE (j : Nat) : E := .bin .add (.reg .x10) (t6E j)
def dBE (j : Nat) : E := .bin .add (.reg .x11) (t6E j)
def lvBRegs (j : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (aBE j)).set .x11
    (dBE j)).set .x29 (aBE j).ld).set .x30 (E.bin .add (aBE j) (.c 8#64)).ld
def lvBMem (j : Nat) : SymMem :=
  [(⟨some (dBE j), 8#64⟩, (E.bin .add (aBE j) (.c 8#64)).ld), (⟨some (dBE j), 0#64⟩, (aBE j).ld)]
def lvBObl (j : Nat) : List Oblig :=
  [.valid ⟨some (dBE j), 8#64⟩ 8, .valid ⟨some (dBE j), 0#64⟩ 8, .valid ⟨some (aBE j), 8#64⟩ 8,
   .valid ⟨some (aBE j), 0#64⟩ 8]
def rLvA (lay : Nat) : Result := [RLvA1.res, RLvA2.res, RLvA3.res].getD (lay - 1) RLvA1.res
def rRT (lay : Nat) : Result := [RRT1.res, RRT2.res, RRT3.res].getD (lay - 1) RRT1.res
def rLvB (lay : Nat) : Result := [RLvB1.res, RLvB2.res, RLvB3.res].getD (lay - 1) RLvB1.res
theorem rLvA_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvA lay = ⟨⟨lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay),
      lvAMem (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay), lvAObl (rootJ lay) (lvDst lay)⟩,
      .c (pcOf (rtAt lay)), .jump, 11, 11⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvA lay) (pcOf (lvAt lay (rootJ lay))) 40 = some (rLvA lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem rRT_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rRT lay = ⟨⟨rtRegs, rtMem, rtObl⟩, .c (pcOf (lvAt lay (rootJ lay) + 11)), .jump, 4, 4⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_rt (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cRT lay) (pcOf (rtAt lay)) 40 = some (rRT lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem rLvB_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvB lay = ⟨⟨lvBRegs (rootJ lay), lvBMem (rootJ lay), lvBObl (rootJ lay)⟩,
      .c (pcOf (lvAt lay (rootJ lay) + 23)), .endOfCode, 12, 12⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvB lay) (pcOf (lvAt lay (rootJ lay) + 11)) 40 = some (rLvB lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- C3 (FULL, E6): the root level (`j = rootJ lay`) copies like any other level and also writes LE64(1) at
window + 24, the encoding row tweak's high word (27 steps: the trampoline adds 4). -/
theorem lvRoot_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay (rootJ lay))) (r : Nat) (hr : r < 2 ^ lvH lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf (lvAt lay (rootJ lay) + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hjl : rootJ lay < lvH lay := by obtain ⟨h1, h4⟩ := hl; unfold rootJ lvH; split_ifs <;> omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : rootJ lay < 7 := by omega
  have hpb := pbE_eval hl hr h20 hp (rootJ lay) hjl
  have hpl := (plan_ok lay r (rootJ lay) hl hr hjl).2
  have hb : r / 2 ^ rootJ lay % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hDp : lvDst lay + 16 * plan lay r (rootJ lay) + 64 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hjl; split_ifs at * <;> omega
  have hS16 : lvSrc lay (rootJ lay) % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  -- abbreviations
  have hslot : (slotE (rootJ lay)).eval s = BitVec.ofNat 64 (16 * plan lay r (rootJ lay)) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  -- piece A: Z low word, then `jal` to the trampoline
  have hrunA := run_lvA lay ⟨h1, h4⟩
  rw [rLvA_eq lay ⟨h1, h4⟩] at hrunA
  have hoblA : Oblig.all s (lvAObl (rootJ lay) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvAObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  have sA := symRun_sound hrunA (code_cLvA hc lay ⟨h1, h4⟩) s hpc hoblA
  generalize ht1 : Result.toState _ s = t1 at sA
  have p1 : t1.pc = pcOf (rtAt lay) := by rw [← ht1]; simp [Result.toState_pc, E.eval]
  have ga : ∀ x : Reg, t1.getReg x = ((lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay)).get x).eval s := by
    intro x; rw [← ht1, Result.toState_getReg]
  have a11 : t1.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, hslot, ofNat_add_ofNat]
    congr 1; ring
  have a10 : t1.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have a30 : t1.getReg .x30 = s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have aR : RegsExcept s t1 [.x6, .x10, .x11, .x29, .x30] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h10, h11, h29, h30⟩ := hx
    rw [ga]
    cases x <;> first | rfl | (exfalso; simp_all)
  have am : ∀ A < 2 ^ 64, t1.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht1]
    simp only [Result.toState_getMem, lvAMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hslot, ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 32
    · subst q; rw [if_pos (by congr 1; ring), if_pos rfl]
    · rw [if_neg (fun h => q (by have := (ofNat_inj hA (by omega)).mp h; omega)), if_neg q]
  -- piece B: the trampoline
  have hrunR := run_rt lay ⟨h1, h4⟩
  rw [rRT_eq lay ⟨h1, h4⟩] at hrunR
  have hoblR : Oblig.all t1 rtObl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [rtObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
  have sR := symRun_sound hrunR (code_cRT hc lay ⟨h1, h4⟩) t1 p1 hoblR
  generalize ht2 : Result.toState _ t1 = t2 at sR
  have p2 : t2.pc = pcOf (lvAt lay (rootJ lay) + 11) := by rw [← ht2]; simp [Result.toState_pc, E.eval]
  have bR : RegsExcept t1 t2 [.x29] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [← ht2, Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  have bm : ∀ A < 2 ^ 64, t2.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
      else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
      else t1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht2]
    simp only [Result.toState_getMem, rtMem, memEval_cons, memEval_nil, Addr.eval, E.eval, a11, a30,
      ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
    · subst q; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => q ((ofNat_inj hA (by omega)).mp h)), if_neg q]
      by_cases q' : A = lvDst lay + 16 * plan lay r (rootJ lay) + 40
      · subst q'; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun h => q' ((ofNat_inj hA (by omega)).mp h)), if_neg q']
  -- piece C: the sibling copy
  have hrunB := run_lvB lay ⟨h1, h4⟩
  rw [rLvB_eq lay ⟨h1, h4⟩] at hrunB
  have h19' : t2.getReg .x19 = BitVec.ofNat 64 r := by
    rw [bR.get (by decide), aR.get (by decide), h19]
  have ht6 := t6E_eval h19' hr7 (rootJ lay) hj7
  have b10 : t2.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by rw [bR.get (by decide), a10]
  have b11 : t2.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [bR.get (by decide), a11]
  have haB : (aBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [aBE, E.eval, BinOp.eval, b10, ht6, ofNat_add_ofNat]
  have hdB : (dBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [dBE, E.eval, BinOp.eval, b11, ht6, ofNat_add_ofNat]
  have hoblB : Oblig.all t2 (lvBObl (rootJ lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvBObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
  have sB := symRun_sound hrunB (code_cLvB hc lay ⟨h1, h4⟩) t2 p2 hoblB
  generalize ht3 : Result.toState _ t2 = t3 at sB
  refine ⟨t3, ((sA.trans sR).trans sB).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · rw [← ht3]; simp [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    have e2 : t2.getReg x = s.getReg x := by
      rw [bR.get (by simp [h29]), aR.get (by simp [h6, h10, h11, h29, h30])]
    rw [← ht3, Result.toState_getReg, ← e2]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    rw [← ht3]
    simp only [Result.toState_getMem, lvBMem, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, haB, hdB,
      ofNat_add_ofNat, BitVec.add_zero]
    have hsrc : ∀ X, lvSrc lay (rootJ lay) ≤ X → X < lvSrc lay (rootJ lay) + 64 →
        t2.getMem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
      intro X hX1 hX2
      rw [bm X (by omega), if_neg (by omega), if_neg (by omega), am X (by omega), if_neg (by omega)]
    rw [hsrc _ (by omega) (by omega), hsrc _ (by omega) (by omega)]
    by_cases q1 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8
    · subst q1
      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h))]
      by_cases q2 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)
      · subst q2
        rw [if_pos rfl, if_neg (by omega), if_neg q1, if_pos rfl]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), bm A hA, am A hA]
        by_cases q3 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
        · rw [if_pos q3, if_pos q3]
        · rw [if_neg q3, if_neg q3, if_neg q1, if_neg q2]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
-- ==== merged from T3M_Expand_NonceBlocks ====
section

/-!
# img-v6 expand: the top-node nonce routine (words 43195 .. 43249, hook 1139; topfold-v6)

Word 1139 (right after the node hash ecall at 1138) is `jal 43195`. For a top node (`a5 = 12`) below the root
(`s4 < 11`) at height `h = s4 + 1` the routine searches the node nonce (64-bit pad at `NODE + 32`): mask the high word
of the kept output half (`NOUT + 16 - 16 * (heap % 2)`), rehash with `pad + 1` while the masked word is nonzero and
`pad + 1 < 104 << h` (the last trial is kept), then clear the pad, store `s2` (the leaf) at `0x66758` and the nonce at
`0x66700 + 8 s4`. Every other node goes straight to 43248 (`addi s6, s6, 16`, the old word 1139) and `jal 1140`.
Block split: research/agents/r3-lean-topbytes/NOTES.md V49.
-/

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest topZeroBits topNonceCap topZeroOk nonceBytes topNodeInput topNodeHashN
  topNonceSearch topNodeAt pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

sym_block nb1139 := symRun { noAlias := true } seg_n1139 (pcOf 1139) 30
sym_block nb1140 := symRun { noAlias := true } seg_1140 (pcOf 1140) 30
sym_block nbA := symRun { noAlias := true } nonce_A (pcOf 43195) 30
sym_block nbB := symRun { noAlias := true } nonce_B (pcOf 43197) 30
sym_block nbC := symRun { noAlias := true } nonce_C (pcOf 43199) 30
sym_block nbZ0 := symRun { noAlias := true } nonce_Z0 (pcOf 54553) 30
sym_block nbZ1 := symRun { noAlias := true } nonce_Z1 (pcOf 54557) 30
sym_block nbZ2 := symRun { noAlias := true } nonce_Z2 (pcOf 54559) 30
sym_block nbZ3 := symRun { noAlias := true } nonce_Z3 (pcOf 54560) 30
sym_block nbZ4 := symRun { noAlias := true } nonce_Z4 (pcOf 54566) 30
sym_block nbZ5 := symRun { noAlias := true } nonce_Z5 (pcOf 54568) 30
sym_block nbG := symRun { noAlias := true } nonce_G (pcOf 43215) 30
sym_block nbL := symRun { noAlias := true } nonce_L (pcOf 43225) 30
sym_block nbH := symRun { noAlias := true } nonce_H (pcOf 43228) 30
sym_block nbI := symRun { noAlias := true } nonce_I (pcOf 43232) 30
sym_block nbJ := symRun { noAlias := true } nonce_J (pcOf 43239) 30
sym_block nbK := symRun { noAlias := true } nonce_K (pcOf 43240) 30
sym_block nbS := symRun { noAlias := true } nonce_S (pcOf 43248) 30

/-- Mask of the zero test on the high word of a top node of height `h` (`1 ≤ h ≤ 11`). T51: the top `b_h` bits
(`b_h = topZeroBits h`; no bit for `b_h = 0`), bits 104..111 (high word bits 40..47) for `h = 11`. -/
def maskE (h : Nat) : Nat :=
  if h = 11 then 255 * 2 ^ 40 else (2 ^ topZeroBits h - 1) * 2 ^ (64 - topZeroBits h)
/-- Cycles of ZB (54553..54568) at height `h`. -/
def zbK (h : Nat) : Nat := if h < 3 then 5 else if h = 3 then 14 else if h = 11 then 15 else 13
/-- The nonce slots and the stored leaf (`0x66700 + 8 k`, `k < 11`, and `0x66758`). -/
def NonceW (A : Nat) : Prop := 0x66700 ≤ A ∧ A < 0x66760

theorem nb_ult (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

section blocks
variable {im : Image} [Code im] (s : MachineState)

theorem n1139_spec (hpc : s.pc = pcOf 1139) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43195 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nb1139 (Code.codeAt_1139 (im := im)) s hpc (by simp [nb1139.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [nb1139.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [nb1139.res, rv_simp] <;> rfl
  · intro A _ _; simp [nb1139.res, rv_simp]

theorem nA_spec (hpc : s.pc = pcOf 43195) (hh : Nat) (hh' : hh < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if hh = 12 then pcOf 43197 else pcOf 43248) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbA (Code.codeAt_nA (im := im)) s hpc (by simp [nbA.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbA.res, E.eval, CmpOp.eval, RegFile.get, h15]
    by_cases hc : hh = 12
    · subst hc; simp
    · have : BitVec.ofNat 64 hh ≠ BitVec.ofNat 64 12 := by rw [Ne, ofNat_inj hh' (by norm_num)]; exact hc
      simp [hc, this]
  · intro r hr; simp at hr; cases r <;> simp_all [nbA.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbA.res, rv_simp]

theorem nB_spec (hpc : s.pc = pcOf 43197) (j : Nat) (hj : j < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 11 ≤ j then pcOf 43248 else pcOf 43199) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbB (Code.codeAt_nB (im := im)) s hpc (by simp [nbB.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbB.res, E.eval, CmpOp.eval, RegFile.get, h20]
    have e := nb_ult j 11 hj (by norm_num)
    by_cases hc : 11 ≤ j
    · simp_all [show ¬ j < 11 by omega]
    · simp_all [show j < 11 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [nbB.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbB.res, rv_simp]

theorem pe_ne' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]

theorem nC_spec (hpc : s.pc = pcOf 43199) (j : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 54553 ∧ t.getReg .x13 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbC (Code.codeAt_nC (im := im)) s hpc (by simp [nbC.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [nbC.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbC.res, rv_simp, h20]; rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [nbC.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbC.res, rv_simp]

theorem zb_bits (h : Nat) (h3 : 4 ≤ h) (h11 : h ≤ 11) :
    topZeroBits h = h - 3 := by interval_cases h <;> rfl

theorem zb0_spec (hpc : s.pc = pcOf 54553) (h : Nat) (h11 : h ≤ 11) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if h < 3 then pcOf 54568 else pcOf 54557) ∧ t.getReg .x14 = 0 ∧
      t.getReg .x31 = 0 ∧ RegsExcept s t [.x14, .x28, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ0 (Code.codeAt_nZ0 (im := im)) s hpc (by simp [nbZ0.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbZ0.res, E.eval, CmpOp.eval, RegFile.get, h13]
    rw [show (3#64 : Word) = BitVec.ofNat 64 3 from rfl, ofNat_slt h 3 (by omega) (by norm_num)]
    by_cases hc : h < 3 <;> simp [hc]
  · simp [nbZ0.res, rv_simp]
  · simp [nbZ0.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [nbZ0.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbZ0.res, rv_simp]

theorem zb1_spec (hpc : s.pc = pcOf 54557) (h : Nat) (h3 : 3 ≤ h) (h11 : h ≤ 11)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if h = 3 then pcOf 54559 else pcOf 54560) ∧
      t.getReg .x14 = BitVec.ofNat 64 (h - 3) ∧ RegsExcept s t [.x14] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ1 (Code.codeAt_nZ1 (im := im)) s hpc (by simp [nbZ1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbZ1.res, rv_simp, h13]
    interval_cases h <;> decide
  · simp only [Result.toState_getReg, nbZ1.res, rv_simp, h13]
    interval_cases h <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbZ1.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbZ1.res, rv_simp]

theorem zb2_spec (hpc : s.pc = pcOf 54559) (h13 : s.getReg .x13 = BitVec.ofNat 64 3) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 54568 ∧ t.getReg .x14 = BitVec.ofNat 64 1 ∧
      t.getReg .x31 = BitVec.ofNat 64 ((2 ^ 1 - 1) * 2 ^ (64 - 1)) ∧
      RegsExcept s t [.x14, .x28, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ2 (Code.codeAt_nZ2 (im := im)) s hpc (by simp [nbZ2.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbZ2.res, E.eval, CmpOp.eval, RegFile.get, h13]; decide
  · simp [nbZ2.res, rv_simp]
  · simp only [Result.toState_getReg, nbZ2.res, rv_simp]; decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbZ2.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbZ2.res, rv_simp]

theorem zb3_x31 (u : MachineState) (h : Nat) (h4 : 4 ≤ h) (h11 : h ≤ 11)
    (h14 : u.getReg .x14 = BitVec.ofNat 64 (h - 3)) :
    (nbZ3.res.toState u).getReg .x31 = BitVec.ofNat 64 ((2 ^ (h - 3) - 1) * 2 ^ (64 - (h - 3))) := by
  simp only [Result.toState_getReg, nbZ3.res, rv_simp, h14]
  interval_cases h <;> decide

theorem zb3_spec (hpc : s.pc = pcOf 54560) (h : Nat) (h4 : 4 ≤ h) (h11 : h ≤ 11)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 (h - 3)) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if h = 11 then pcOf 54566 else pcOf 54568) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((2 ^ (h - 3) - 1) * 2 ^ (64 - (h - 3))) ∧
      RegsExcept s t [.x28, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ3 (Code.codeAt_nZ3 (im := im)) s hpc (by simp [nbZ3.res, rv_simp]), ?_,
    zb3_x31 s h h4 h11 h14, ?_, ?_⟩
  · simp only [Result.toState_pc, nbZ3.res, E.eval, CmpOp.eval, RegFile.get, h13]
    rw [show (11#64 : Word) = BitVec.ofNat 64 11 from rfl, pe_ne' (by omega) (by norm_num)]
    by_cases hc : h = 11 <;> simp [hc]
  · intro r hr; simp at hr; cases r <;> simp_all [nbZ3.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbZ3.res, rv_simp]

theorem zb4_spec (hpc : s.pc = pcOf 54566) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 43215 ∧ t.getReg .x31 = BitVec.ofNat 64 (255 * 2 ^ 40) ∧
      RegsExcept s t [.x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ4 (Code.codeAt_nZ4 (im := im)) s hpc (by simp [nbZ4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [nbZ4.res, E.eval]
  · simp only [Result.toState_getReg, nbZ4.res, rv_simp]; decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbZ4.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbZ4.res, rv_simp]

theorem zb5_spec (hpc : s.pc = pcOf 54568) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43215 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbZ5 (Code.codeAt_nZ5 (im := im)) s hpc (by simp [nbZ5.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, nbZ5.res, E.eval]
  · intro r hr; cases r <;> rfl
  · intro A _ _; rfl

/-- T51 ZB: `x14 = b_h`, `x31 = maskE h`, then `j 43215`. -/
theorem nZ_spec (hpc : s.pc = pcOf 54553) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s (zbK h) (zbK h) t ∧ t.pc = pcOf 43215 ∧ t.getReg .x14 = BitVec.ofNat 64 (topZeroBits h) ∧
      t.getReg .x31 = BitVec.ofNat 64 (maskE h) ∧ RegsExcept s t [.x14, .x28, .x31] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u0, s0, p0, a14, a31, r0, f0⟩ := zb0_spec (im := im) s hpc h h11 h13
  have u013 : u0.getReg .x13 = BitVec.ofNat 64 h := by rw [r0.get (by simp)]; exact h13
  by_cases hl3 : h < 3
  · rw [if_pos hl3] at p0
    obtain ⟨v, sv, pv, rv, fv⟩ := zb5_spec (im := im) u0 p0
    have hb : topZeroBits h = 0 := by interval_cases h <;> rfl
    refine ⟨v, (s0.trans sv).of_eq (by simp [zbK, hl3]) (by simp [zbK, hl3]), pv, ?_, ?_, ?_, ?_⟩
    · rw [rv.get (by simp), a14, hb]; rfl
    · rw [rv.get (by simp), a31, maskE, if_neg (by omega), hb]; rfl
    · exact (r0.trans rv).mono (by simp)
    · exact (f0.trans fv).mono (fun A _ h => by simp_all)
  rw [if_neg hl3] at p0
  obtain ⟨u1, s1, p1, b14, r1, f1⟩ := zb1_spec (im := im) u0 p0 h (by omega) h11 u013
  have u113 : u1.getReg .x13 = BitVec.ofNat 64 h := by rw [r1.get (by simp)]; exact u013
  by_cases h3 : h = 3
  · rw [if_pos h3] at p1
    obtain ⟨u2, s2, p2, c14, c31, r2, f2⟩ := zb2_spec (im := im) u1 p1 (by rw [u113, h3])
    obtain ⟨v, sv, pv, rv, fv⟩ := zb5_spec (im := im) u2 p2
    have hb : topZeroBits h = 1 := by rw [h3]; rfl
    refine ⟨v, (((s0.trans s1).trans s2).trans sv).of_eq (by simp [zbK, hl3, h3]) (by simp [zbK, hl3, h3]), pv,
      ?_, ?_, ?_, ?_⟩
    · rw [rv.get (by simp), c14, hb]
    · rw [rv.get (by simp), c31, maskE, if_neg (by omega), hb]
    · exact (((r0.trans r1).trans r2).trans rv).mono (by simp)
    · exact (((f0.trans f1).trans f2).trans fv).mono (fun A _ h => by simp_all)
  rw [if_neg h3] at p1
  obtain ⟨u2, s2, p2, c31, r2, f2⟩ := zb3_spec (im := im) u1 p1 h (by omega) h11 u113 b14
  have hb : topZeroBits h = h - 3 := zb_bits h (by omega) h11
  have u214 : u2.getReg .x14 = BitVec.ofNat 64 (h - 3) := by rw [r2.get (by simp)]; exact b14
  by_cases h11' : h = 11
  · rw [if_pos h11'] at p2
    obtain ⟨v, sv, pv, d31, rv, fv⟩ := zb4_spec (im := im) u2 p2
    refine ⟨v, (((s0.trans s1).trans s2).trans sv).of_eq (by simp [zbK, hl3, h3, h11']) (by simp [zbK, hl3, h3, h11']),
      pv, ?_, ?_, ?_, ?_⟩
    · rw [rv.get (by simp), u214, hb]
    · rw [d31, maskE, if_pos h11']
    · exact (((r0.trans r1).trans r2).trans rv).mono (by simp)
    · exact (((f0.trans f1).trans f2).trans fv).mono (fun A _ h => by simp_all)
  rw [if_neg h11'] at p2
  obtain ⟨v, sv, pv, rv, fv⟩ := zb5_spec (im := im) u2 p2
  refine ⟨v, (((s0.trans s1).trans s2).trans sv).of_eq (by simp [zbK, hl3, h3, h11']) (by simp [zbK, hl3, h3, h11']),
    pv, ?_, ?_, ?_, ?_⟩
  · rw [rv.get (by simp), u214, hb]
  · rw [rv.get (by simp), c31, maskE, if_neg h11', hb]
  · exact (((r0.trans r1).trans r2).trans rv).mono (by simp)
  · exact (((f0.trans f1).trans f2).trans fv).mono (fun A _ h => by simp_all)

theorem nG_spec (hpc : s.pc = pcOf 43215) (h b leaf : Nat) (hh : h ≤ 11) (hb : b ≤ 11) (hl : leaf < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 b)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 43225 ∧ t.getReg .x17 = BitVec.ofNat 64 (104 * 2 ^ b) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (leaf / 2 ^ h % 2)) ∧
      RegsExcept s t [.x17, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbG (Code.codeAt_nG (im := im)) s hpc (by simp [nbG.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [nbG.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbG.res, rv_simp, h14]
    interval_cases b <;> decide
  · simp only [Result.toState_getReg, nbG.res, rv_simp, h13, h18]
    rw [toNat_ofNat_lt (show h < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show h < 64 by omega), ofNat_shr _ _ hl,
      ofNat_and1]
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ h) with hb | hb <;> rw [hb] <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbG.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbG.res, rv_simp]

theorem nL_spec (hpc : s.pc = pcOf 43225) (X : Nat) (hX : X = NOUT ∨ X = NOUT + 16)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (X + 8)) &&& s.getReg .x31) = 0#64 then pcOf 43240 else pcOf 43228) ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s nbL.res.st.obl := by
    rcases hX with rfl | rfl <;> simp only [nbL.res] <;> t3n [h29, NOUT] <;> try decide
  refine ⟨_, symRun_sound nbL (Code.codeAt_nL (im := im)) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbL.res, E.eval, CmpOp.eval, RegFile.get]
    t3n [h29]
    split_ifs <;> simp_all
  · intro r hr; simp at hr; cases r <;> simp_all [nbL.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbL.res, rv_simp]

theorem nH_spec (hpc : s.pc = pcOf 43228) (n c : Nat) (hn : n + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (hpad : s.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if c ≤ n + 1 then pcOf 43240 else pcOf 43232) ∧
      t.getReg .x28 = BitVec.ofNat 64 0x20000 ∧ t.getReg .x30 = BitVec.ofNat 64 (n + 1) ∧
      RegsExcept s t [.x28, .x30] ∧ Frame s t (fun _ => False) := by
  have hobl : Oblig.all s nbH.res.st.obl := by
    simp only [nbH.res]
    t3n []
  refine ⟨_, symRun_sound nbH (Code.codeAt_nH (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbH.res, E.eval, CmpOp.eval, RegFile.get, h17]
    t3n [hpad]
    rw [nb_ult (n + 1) c hn hc]
    by_cases hcn : c ≤ n + 1
    · simp [hcn, show ¬ n + 1 < c by omega]
    · simp [hcn, show n + 1 < c by omega]
  · simp [nbH.res, rv_simp]
  · simp only [Result.toState_getReg, nbH.res]
    t3n [hpad]
  · intro r hr; simp at hr; cases r <;> simp_all [nbH.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbH.res, rv_simp]

theorem nI_spec (hpc : s.pc = pcOf 43232) (h28 : s.getReg .x28 = BitVec.ofNat 64 0x20000) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 43238 ∧ t.getMem (BitVec.ofNat 64 (NODE + 32)) = s.getReg .x30 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun X => X = NODE + 32) := by
  have hobl : Oblig.all s nbI.res.st.obl := by
    simp only [nbI.res]
    t3n [h28]
    try decide
  refine ⟨_, symRun_sound nbI (Code.codeAt_nI (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [nbI.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, nbI.res, NODE]
    t3n [h28]
  · simp [nbI.res, rv_simp]
  · simp [nbI.res, rv_simp]
  · simp [nbI.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [nbI.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, nbI.res]
    t3n [h28]
    rw [if_neg (by omega)]

theorem fetch_n43238 (hpc : s.pc = pcOf 43238) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_n43238 (im := im)).fetch s hpc).trans rfl

theorem nJ_spec (hpc : s.pc = pcOf 43239) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43225 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbJ (Code.codeAt_nJ (im := im)) s hpc (by simp [nbJ.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [nbJ.res, Result.toState_pc, E.eval]
  · intro r hr; cases r <;> simp_all [nbJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbJ.res, rv_simp]

theorem nK_spec (hpc : s.pc = pcOf 43240) (j : Nat) (hj : j < 11) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf 43248 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x66758) = s.getReg .x18 ∧
      t.getMem (BitVec.ofNat 64 (0x66700 + 8 * j)) = s.getMem (BitVec.ofNat 64 (NODE + 32)) ∧
      RegsExcept s t [.x28, .x29, .x30] ∧
      Frame s t (fun X => X = NODE + 32 ∨ X = 0x66758 ∨ X = 0x66700 + 8 * j) := by
  have hobl : Oblig.all s nbK.res.st.obl := by
    simp only [nbK.res]
    t3n [h20]
    all_goals omega
  refine ⟨_, symRun_sound nbK (Code.codeAt_nK (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [nbK.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getMem, nbK.res, NODE]
    t3n [h20]
    split_ifs <;> first | rfl | omega
  · simp only [Result.toState_getMem, nbK.res]
    t3n [h20]
    split_ifs <;> first | rfl | omega
  · simp only [Result.toState_getMem, nbK.res, NODE]
    t3n [h20]
    split_ifs <;> first | rfl | omega | (congr 1; omega)
  · intro r hr; simp at hr; cases r <;> simp_all [nbK.res, rv_simp] <;> rfl
  · intro X hX hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, nbK.res]
    t3n [h20]
    split_ifs <;> first | rfl | omega

theorem nS_spec (hpc : s.pc = pcOf 43248) (P : Nat) (h22 : s.getReg .x22 = BitVec.ofNat 64 P) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1140 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      RegsExcept s t [.x22] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbS (Code.codeAt_nS (im := im)) s hpc (by simp [nbS.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [nbS.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbS.res, rv_simp, h22, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [nbS.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbS.res, rv_simp]

theorem n1140_spec (hpc : s.pc = pcOf 1140) (M j : Nat) (hM : 64 ≤ M) (hM' : M < 2 ^ 64)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 M) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1076 ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nb1140 (Code.codeAt_1140 (im := im)) s hpc (by simp [nb1140.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, nb1140.res, E.eval]
  · simp only [Result.toState_getReg, nb1140.res, rv_simp, h24]
    apply BitVec.eq_of_toNat_eq
    first
      | (rw [BitVec.toNat_sub, toNat_ofNat_lt hM', toNat_ofNat_lt (show M - 64 < 2 ^ 64 by omega),
          show (64#64 : Word).toNat = 64 from rfl]; omega)
      | (rw [BitVec.toNat_add, toNat_ofNat_lt hM', toNat_ofNat_lt (show M - 64 < 2 ^ 64 by omega)]; simp; omega)
  · simp only [Result.toState_getReg, nb1140.res, rv_simp, h20, ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [nb1140.res, rv_simp] <;> rfl
  · intro A _ _; simp [nb1140.res, rv_simp]

end blocks
end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_NonceLoop ====
section

/-!
# img-v6 expand: the top-node nonce search as a bounded refinement (topfold-v6)

`nonce_run`: after the first node hash (answer `a`, trial 0) the routine 1139 .. 43249 + 1140 .. 1142 refines
`trialTail h heap l r (topNonceCap h - 1) 0 (projHalf _ a)`, i.e. the tail of `T3.topNodeAt h heap l r`, with at most
`29 + 22 * (topNonceCap h - 1) + 20` cycles, and leaves the nonce at `0x66700 + 8 (h - 1)`, the leaf at `0x66758`
and the pad `NODE + 32` cleared. `skip_spec`: the other nodes (lower layers, top root) take 8 or 10 cycles.
Template: T3M/Keygen/TopTree.lean (keygen's nonce search).
-/

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest topZeroBits topNonceCap topZeroOk nonceBytes topNodeInput topNodeHashN
  topNonceSearch topNodeAt pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Arithmetic of the zero test and the node input (copied from Keygen.TopTree) -/
theorem ne_land_mask_eq_zero (n k w : Nat) :
    n &&& ((2 ^ w - 1) * 2 ^ k) = 0 ↔ n / 2 ^ k % 2 ^ w = 0 := by
  have hM : (2 ^ w - 1) * 2 ^ k = (2 ^ w - 1) <<< k := by rw [Nat.shiftLeft_eq]
  rw [hM]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    have := congrArg (fun y => Nat.testBit y (j + k)) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at this
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases hj : j < w
    · have e : j + k - k = j := by omega
      simp only [e, hj, decide_true, Bool.and_true, ge_iff_le, Nat.le_add_left] at this
      simp [hj, this]
    · simp [hj]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hik : k ≤ i
    · by_cases hiw : i - k < w
      · have := congrArg (fun y => Nat.testBit y (i - k)) h
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, hiw, decide_true,
          Bool.true_and] at this
        rw [show i - k + k = i by omega] at this
        simp [this]
      · simp [hiw]
    · simp [hik]
theorem ne_hiword_toNat (v : BitVec 128) : (v.extractLsb' 64 64).toNat = v.toNat / 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.mod_eq_of_lt
  omega
theorem ne_zero_test_hi (v : BitVec 128) (b : Nat) (hb : b ≤ 64) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) = 0#64) ↔
      v.toNat / 2 ^ (128 - b) = 0 := by
  have hlt : (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ 64 := by
    have h1 : 2 ^ b - 1 < 2 ^ b := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
    calc (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ b * 2 ^ (64 - b) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 + (64 - b) = 128 - b by omega]
  have hv : v.toNat / 2 ^ (128 - b) < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show b + (128 - b) = 128 by omega]
    exact v.isLt
  rw [Nat.mod_eq_of_lt hv]
theorem ne_zero_test_bits98 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 11 - 1) * 2 ^ 34) = 0#64) ↔
      v.toNat / 2 ^ 98 % 2 ^ 11 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- Campaign T51: the top zero bits are `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`; restated). -/
theorem ne_topZeroBits_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    topZeroBits h = SigGolfCandidate.T3.topZeroAlloc.getD h 0 := rfl

/-- The machine's zero test (43225..43227) is `topZeroOk`. -/
theorem ne_zero_test_bits104 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) = 0#64) ↔
      v.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- The machine's zero test (43225..43227, mask from ZB 54553) is `topZeroOk`. -/
theorem ne_zero_test (v : Digest) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 (maskE h) = 0#64) ↔ topZeroOk h v = true := by
  unfold maskE topZeroOk
  by_cases hc : h = 11
  · rw [if_pos hc, if_pos hc, show (255 : Nat) * 2 ^ 40 = (2 ^ 8 - 1) * 2 ^ 40 by norm_num, ne_zero_test_bits104,
      beq_iff_eq]
  · have hb : topZeroBits h ≤ 64 := by interval_cases h <;> decide
    rw [if_neg hc, if_neg hc, ne_zero_test_hi v _ hb, beq_iff_eq]

theorem ne_nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl
theorem ne_topNodeInput_length (heap n : Nat) (l r : Digest) : (topNodeInput heap n l r).length = 64 := by
  simp [topNodeInput, nonceBytes, bytesLE_length]
theorem ne_wordsOf_topNodeInput (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64) (l r : Digest) :
    wordsOf (topNodeInput heap n l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 heap, 0, BitVec.ofNat 64 n, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold topNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, nonceBytes]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ne_nonce_words n hn,
    wordsOf_bytesLE16, Keygen.nodeTweak_3_top 0 heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (Keygen.nodeLo 0 0 + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]
  simp [Keygen.nodeLo]
theorem ne_topNodeInput_blocks (heap n : Nat) (l r : Digest) :
    (toQ (pad64 (topNodeInput heap n l r))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ne_topNodeInput_length]),
    blocks_toQ ⟨by rw [ne_topNodeInput_length]; omega, by rw [ne_topNodeInput_length]⟩, ne_topNodeInput_length]
theorem ne_hashInput_topNode (t : MachineState) (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64)
    (l r : Digest) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODE) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (w0 : t.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64)
    (w8 : t.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64)
    (w16 : t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap)
    (w24 : t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0)
    (w32 : t.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (w40 : t.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (w48 : t.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64)
    (w56 : t.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64) :
    hashInput t = toQ (pad64 (topNodeInput heap n l r)) := by
  rw [pad64_of_aligned _ (by rw [ne_topNodeInput_length])]
  refine hashInput_toQ t _ 0 NODE (ne_topNodeInput_length _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [ne_wordsOf_topNodeInput heap n h1 h2 hn, readWords_eight, w0, w8, w16, w24, w32, w40, w48, w56]
theorem ne_out_after_hash (t : MachineState) (a : BitVec 256) (heap : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 NOUT) :
    DigAt (writeHash t a) (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  rw [T3.nodeHalfHigh_top]
  rcases Nat.mod_two_eq_zero_or_one heap with hp | hp
  · have hd : decide (heap % 2 = 0) = true := by simp [hp]
    rw [hd, T3.projHalf_true, hp, show NOUT + 16 - 16 * 0 = NOUT + 16 from rfl]
    exact DigAt.writeHash_hi t a NOUT h12 (by decide)
  · have hd : decide (heap % 2 = 0) = false := by simp [hp]
    rw [hd, T3.projHalf_false, hp, show NOUT + 16 - 16 * 1 = NOUT from rfl]
    exact DigAt.writeHash_lo t a NOUT h12 (by decide)

/-- What follows the trial-`n` hash in `topNonceSearch` (fuel = trials left). -/
def neTrialTail (h heap : Nat) (l r : Digest) : Nat → Nat → Digest → T3.M (Nat × Digest)
  | 0, n, v => pure (n, v)
  | fuel + 1, n, v => if topZeroOk h v then pure (n, v) else topNonceSearch h heap l r fuel (n + 1)
theorem ne_topNonceSearch_eq (h heap : Nat) (l r : Digest) (fuel n : Nat) :
    topNonceSearch h heap l r fuel n = topNodeHashN heap n l r >>= neTrialTail h heap l r fuel n := by
  cases fuel <;> rfl
theorem ne_topNodeHashN_bind {β : Type} (heap n : Nat) (l r : Digest) (g : Digest → T3.M β) :
    topNodeHashN heap n l r >>= g =
      T3.publicHash (topNodeInput heap n l r) >>= fun a => g (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold topNodeHashN T3.projHash; rw [bind_assoc]; simp only [pure_bind]
theorem ne_topNonceCap_le (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    1 ≤ topNonceCap h ∧ topNonceCap h ≤ 104 * 2048 := by
  interval_cases h <;> decide
/-- Campaign T51: the cap is `104 << b_h` (#938: `104 << h`; restated). -/
theorem ne_topNonceCap_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : topNonceCap h = 104 * 2 ^ topZeroBits h := rfl

theorem ne_nonceBytes_zero : nonceBytes 0 = zero16 := by decide

section sim
variable {α β : Type} {image : Image} {sk : BitVec 256}
theorem ne_tb_pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem ne_tb_publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
end sim

section run
variable {im : Image} [Code im] {sk : BitVec 256}

/-! ## The skip path (lower layers and the top root) -/
theorem skip_spec (s : MachineState) (hpc : s.pc = pcOf 1139) (hh j P M : Nat) (hh' : hh < 2 ^ 64)
    (hj : j < 2 ^ 63) (hM : 64 ≤ M) (hM' : M < 2 ^ 64) (hskip : hh ≠ 12 ∨ 11 ≤ j)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t k, Steps im s k k t ∧ k ≤ 10 ∧ t.pc = pcOf 1076 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x22, .x24, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := n1139_spec (im := im) s hpc
  obtain ⟨t2, s2, p2, r2, f2⟩ := nA_spec (im := im) t1 p1 hh hh' (by rw [r1.get (by simp)]; exact h15)
  have r12 : RegsExcept s t2 [.x28] := (r1.trans r2).mono (by decide)
  obtain ⟨t3, k3, s3, hk3, p3, r3, f3⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧ k3 ≤ 2 ∧ t3.pc = pcOf 43248 ∧
      RegsExcept t2 t3 [.x28] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hc : hh = 12
    · rw [if_pos hc] at p2
      obtain ⟨t3, s3, p3, r3, f3⟩ := nB_spec (im := im) t2 p2 j (by omega) (by rw [r12.get (by simp)]; exact h20)
      rw [if_pos (by omega)] at p3
      exact ⟨t3, 2, s3, le_rfl, p3, r3, f3⟩
    · rw [if_neg hc] at p2
      exact ⟨t2, 0, Steps.refl _, by omega, p2, RegsExcept.refl _ _, Frame.refl _ _⟩
  have r13 : RegsExcept s t3 [.x28] := (r12.trans r3).mono (by decide)
  obtain ⟨t4, s4, p4, x22, r4, f4⟩ := nS_spec (im := im) t3 p3 P (by rw [r13.get (by simp)]; exact h22)
  obtain ⟨t5, s5, p5, x24, x20, r5, f5⟩ := n1140_spec (im := im) t4 p4 M j hM hM'
    (by rw [r4.get (by simp), r13.get (by simp)]; exact h24) (by rw [r4.get (by simp), r13.get (by simp)]; exact h20)
  refine ⟨t5, 1 + 2 + k3 + 2 + 3, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
    by rw [r5.get (by simp)]; exact x22, x24, x20, ?_, ?_⟩
  · exact ((r13.trans r4).trans r5).mono (by decide)
  · exact ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun _ _ h => by simp_all)

/-! ## The nonce path -/
/-- Cycles of the setup 1139 .. 43224 at height `h` (T51: 43199/43200 `j 54553`, ZB 54553..54568, `j 43215`). -/
def nsetupK (h : Nat) : Nat := 17 + zbK h
theorem nsetupK_le (h : Nat) : nsetupK h ≤ 32 := by unfold nsetupK zbK; split_ifs <;> omega
theorem nsetup_spec (s : MachineState) (hpc : s.pc = pcOf 1139) (j leaf : Nat) (hj : j < 11) (hl : leaf < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 12) (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s (nsetupK (j + 1)) (nsetupK (j + 1)) t ∧ t.pc = pcOf 43225 ∧
      t.getReg .x31 = BitVec.ofNat 64 (maskE (j + 1)) ∧ t.getReg .x17 = BitVec.ofNat 64 (topNonceCap (j + 1)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (leaf / 2 ^ (j + 1) % 2)) ∧
      RegsExcept s t [.x13, .x14, .x17, .x28, .x29, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := n1139_spec (im := im) s hpc
  obtain ⟨t2, s2, p2, r2, f2⟩ := nA_spec (im := im) t1 p1 12 (by norm_num) (by rw [r1.get (by simp)]; exact h15)
  rw [if_pos rfl] at p2
  have r12 : RegsExcept s t2 [.x28] := (r1.trans r2).mono (by decide)
  obtain ⟨t3, s3, p3, r3, f3⟩ := nB_spec (im := im) t2 p2 j (by omega) (by rw [r12.get (by simp)]; exact h20)
  rw [if_neg (by omega)] at p3
  have r13 : RegsExcept s t3 [.x28] := (r12.trans r3).mono (by decide)
  obtain ⟨t4, s4, p4, x13, r4, f4⟩ := nC_spec (im := im) t3 p3 j (by rw [r13.get (by simp)]; exact h20)
  obtain ⟨t5, s5, p5, x14, x31, r5, f5⟩ := nZ_spec (im := im) t4 p4 (j + 1) (by omega) (by omega) x13
  have hb : topZeroBits (j + 1) ≤ 11 := by interval_cases j <;> decide
  obtain ⟨t8, s8, p8, x17, x29, r8, f8⟩ := nG_spec (im := im) t5 p5 (j + 1) (topZeroBits (j + 1)) leaf (by omega) hb hl
    (by rw [r5.get (by simp)]; exact x13) x14
    (by rw [r5.get (by simp), r4.get (by simp), r13.get (by simp)]; exact h18)
  refine ⟨t8, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s8)).of_eq
      (by unfold nsetupK; omega) (by unfold nsetupK; omega),
    p8, by rw [r8.get (by simp)]; exact x31, ?_, x29, ?_, ?_⟩
  · rw [x17, ne_topNonceCap_eq _ (by omega) (by omega)]
  · exact (((r13.trans r4).trans r5).trans r8).mono (by decide)
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f8).mono
      (fun _ _ h => by simp_all)

/-- The state right before the first node hash (at 1138): arguments, node words, climb registers. -/
structure NFacts (t2 : MachineState) (heap leaf j P M : Nat) (l r : Digest) : Prop where
  x5 : t2.getReg .x5 = 0
  x12 : t2.getReg .x12 = BitVec.ofNat 64 NOUT
  x15 : t2.getReg .x15 = BitVec.ofNat 64 12
  x18 : t2.getReg .x18 = BitVec.ofNat 64 leaf
  x20 : t2.getReg .x20 = BitVec.ofNat 64 j
  x22 : t2.getReg .x22 = BitVec.ofNat 64 P
  x24 : t2.getReg .x24 = BitVec.ofNat 64 M
  w0 : t2.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64
  w8 : t2.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64
  w16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap
  w24 : t2.getMem (BitVec.ofNat 64 (NODE + 24)) = 0
  w32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  w40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  w48 : t2.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64
  w56 : t2.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64
  h1 : 1 ≤ heap
  h2 : heap < 4096
  hj : j < 11
  hpar : leaf / 2 ^ (j + 1) % 2 = heap % 2
  hl : leaf < 2 ^ 64
  hM : 64 ≤ M
  hM' : M < 2 ^ 64

def nTrialRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x17, .x28, .x29, .x30, .x31]
def NTrialW (X : Nat) : Prop := X = NODE + 32 ∨ (NOUT ≤ X ∧ X < NOUT + 32)

/-- At 43225 after the trial-`n` hash (answer `a`). -/
structure NTrialSt (t2 : MachineState) (h heap n : Nat) (a : BitVec 256) (u : MachineState) : Prop where
  pc : u.pc = pcOf 43225
  regs : RegsExcept t2 u nTrialRegs
  x31 : u.getReg .x31 = BitVec.ofNat 64 (maskE h)
  x17 : u.getReg .x17 = BitVec.ofNat 64 (topNonceCap h)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (heap % 2))
  pad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n
  frame : Frame t2 u NTrialW
  out : DigAt u (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)

def nExitRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x17, .x20, .x22, .x24, .x28, .x29, .x30, .x31]
def NExitW (j : Nat) (X : Nat) : Prop := (NOUT ≤ X ∧ X < NOUT + 32) ∨ X = 0x66758 ∨ X = 0x66700 + 8 * j

/-- Back at 1076 with the node value kept, the nonce recorded and the pad cleared. -/
structure NPost (t2 : MachineState) (heap leaf j P M : Nat) (res : Nat × Digest) (w : MachineState) : Prop where
  pc : w.pc = pcOf 1076
  x20 : w.getReg .x20 = BitVec.ofNat 64 (j + 1)
  x22 : w.getReg .x22 = BitVec.ofNat 64 (P + 16)
  x24 : w.getReg .x24 = BitVec.ofNat 64 (M - 64)
  pad : w.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  leafAt : w.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf
  nonceAt : w.getMem (BitVec.ofNat 64 (0x66700 + 8 * j)) = BitVec.ofNat 64 res.1
  out : DigAt w (NOUT + 16 - 16 * (heap % 2)) res.2
  regs : RegsExcept t2 w nExitRegs
  frame : Frame t2 w (NExitW j)

theorem n_exit {t2 u : MachineState} {heap leaf j P M : Nat} {l r : Digest} (F : NFacts t2 heap leaf j P M l r)
    (hpc : u.pc = pcOf 43240) {L : List Reg} (hL : ∀ x ∈ L, x ∈ nTrialRegs) (hr : RegsExcept t2 u L)
    (hf : Frame t2 u NTrialW) {n : Nat} (hpad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    {v : Digest} (hv : DigAt u (NOUT + 16 - 16 * (heap % 2)) v) :
    ∃ w, Steps im u 13 13 w ∧ NPost t2 heap leaf j P M (n, v) w := by
  have g : ∀ x, x ∉ nTrialRegs → u.getReg x = t2.getReg x := fun x hx => hr.get (fun hm => hx (hL x hm))
  have hj := F.hj
  obtain ⟨u1, s1, p1, m32, m58, mj, r1, f1⟩ := nK_spec (im := im) u hpc j hj
    (by rw [g _ (by simp [nTrialRegs])]; exact F.x20)
  obtain ⟨u2, s2, p2, x22, r2, f2⟩ := nS_spec (im := im) u1 p1 P
    (by rw [r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x22)
  obtain ⟨w, s3, p3, x24, x20, r3, f3⟩ := n1140_spec (im := im) u2 p2 M j F.hM F.hM'
    (by rw [r2.get (by simp), r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x24)
    (by rw [r2.get (by simp), r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x20)
  have f23 : Frame u1 w (fun _ => False) := (f2.trans f3).mono (fun _ _ h => by simp_all)
  have hpar := F.hpar
  have hoff : NOUT + 16 - 16 * (heap % 2) + 16 ≤ NOUT + 32 := by simp only [NOUT]; omega
  refine ⟨w, (s1.trans s2).trans s3, ⟨p3, x20, by rw [r3.get (by simp)]; exact x22, x24, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [f23.get (by decide) (fun h => h), m32]
  · rw [f23.get (by decide) (fun h => h), m58, g _ (by simp [nTrialRegs]), F.x18]
  · rw [f23.get (by omega) (fun h => h), mj, hpad]
  · refine (hv.frame f1 (by simp only [NOUT]; omega) ?_ ?_).frame f23 (by simp only [NOUT]; omega)
      (fun h => h) (fun h => h)
    all_goals (simp only [NOUT, NODE]; omega)
  · exact (((hr.mono hL).trans r1).trans (r2.trans r3)).mono (by decide)
  · intro A hA hn
    unfold NExitW at hn
    by_cases h32 : A = NODE + 32
    · subst h32
      rw [f23.get (by decide) (fun h => h), m32, F.w32]
    · rw [f23.get hA (fun h => h), f1.get hA (by simp only [NODE] at h32 ⊢; omega),
        hf.get hA (by unfold NTrialW; simp only [NODE, NOUT] at h32 hn ⊢; omega)]

section loop
variable (sk) {t2 : MachineState} {heap leaf j P M : Nat} {l r : Digest} (F : NFacts t2 heap leaf j P M l r)
include F

theorem n_check {n : Nat} {a : BitVec 256} {u : MachineState} (hu : NTrialSt t2 (j + 1) heap n a u) :
    ∃ u1, Steps im u 3 3 u1 ∧
      u1.pc = (if topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true then pcOf 43240
        else pcOf 43228) ∧
      RegsExcept u u1 [.x30] ∧ Frame u u1 (fun _ => False) := by
  have hj := F.hj
  have hX : NOUT + 16 - 16 * (heap % 2) = NOUT ∨ NOUT + 16 - 16 * (heap % 2) = NOUT + 16 := by
    rcases Nat.mod_two_eq_zero_or_one heap with h | h <;> rw [h] <;> simp
  obtain ⟨u1, s1, p1, r1, f1⟩ := nL_spec (im := im) u hu.pc _ hX hu.x29
  refine ⟨u1, s1, ?_, r1, f1⟩
  rw [p1, hu.x31, hu.out.2]
  by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
  · rw [if_pos ((ne_zero_test _ (j + 1) (by omega) (by omega)).mpr hz), if_pos hz]
  · rw [if_neg (fun hc => hz ((ne_zero_test _ (j + 1) (by omega) (by omega)).mp hc)), if_neg hz]

theorem n_trial_loop : ∀ fuel n (a : BitVec 256) u, NTrialSt t2 (j + 1) heap n a u →
    n + fuel + 1 = topNonceCap (j + 1) →
    TBSim im sk u (22 * fuel + 20)
      (neTrialTail (j + 1) heap l r fuel n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => NPost t2 heap leaf j P M res w) := by
  have hj := F.hj
  have hcap := ne_topNonceCap_le (j + 1) (by omega) (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := n_check (im := im) F hu
    by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p1 (L := nTrialRegs ++ [.x30]) (by simp [nTrialRegs])
        (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, -, -, r2, f2⟩ := nH_spec (im := im) u1 p1 n (topNonceCap (j + 1)) (by omega) (by omega)
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad) (by rw [r1.get (by simp)]; exact hu.x17)
      rw [if_pos (by omega)] at p2
      have f12 : Frame u u2 (fun _ => False) := (f1.trans f2).mono (fun X _ h => by simp_all)
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p2 (L := nTrialRegs ++ [.x30] ++ [.x28, .x30])
        (by simp [nTrialRegs]) ((hu.regs.trans r1).trans r2)
        ((hu.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f12.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f12 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans (s2.trans sw)) hw).mono (by omega)
        (fun _ _ h => h)
  | succ fuel ih =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := n_check (im := im) F hu
    by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p1 (L := nTrialRegs ++ [.x30]) (by simp [nTrialRegs])
        (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      have e : neTrialTail (j + 1) heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          pure (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by simp only [neTrialTail, hz, if_true]
      rw [e]
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, x28_2, x30_2, r2, f2⟩ := nH_spec (im := im) u1 p1 n (topNonceCap (j + 1)) (by omega)
        (by omega) (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad) (by rw [r1.get (by simp)]; exact hu.x17)
      rw [if_neg (by omega)] at p2
      obtain ⟨u3, s3, p3, m32_3, x10_3, x11_3, x12_3, r3, f3⟩ := nI_spec (im := im) u2 p2 x28_2
      have r03 : RegsExcept t2 u3 (nTrialRegs ++ [.x30] ++ [.x28, .x30] ++ [.x10, .x11, .x12]) :=
        ((hu.regs.trans r1).trans r2).trans r3
      have g3 : ∀ x, x ∉ nTrialRegs → u3.getReg x = t2.getReg x := fun x hx => r03.get (fun hm => hx
        ((by decide : ∀ y ∈ nTrialRegs ++ [Reg.x30] ++ [.x28, .x30] ++ [.x10, .x11, .x12], y ∈ nTrialRegs) x hm))
      have f03 : Frame t2 u3 NTrialW := (((hu.frame.trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h
        · exact h
        · exact h.elim
        · exact h.elim
        · exact Or.inl h)
      have fr : ∀ X, X < 2 ^ 64 → ¬ NTrialW X → u3.getMem (BitVec.ofNat 64 X) = t2.getMem (BitVec.ofNat 64 X) :=
        fun X hX hn => f03.get hX hn
      have nW : ∀ X, X < NODE + 32 ∨ (NODE + 32 < X ∧ X < NOUT) → ¬ NTrialW X := by
        intro X hX hw; unfold NTrialW at hw; simp only [NODE, NOUT] at hX hw; omega
      have hq : hashInput u3 = toQ (pad64 (topNodeInput heap (n + 1) l r)) :=
        ne_hashInput_topNode u3 heap (n + 1) F.h1 F.h2 (by omega) l r x10_3 x11_3
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w0])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w8])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w16])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w24])
          (by rw [m32_3, x30_2])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w40])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w48])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w56])
      have hv : hashArgumentsValid u3 = true :=
        hashArgs_const u3 NODE 64 NOUT x10_3 x11_3 x12_3 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h5 : u3.getReg .x5 = 0 := by rw [g3 _ (by simp [nTrialRegs]), F.x5]
      have e : neTrialTail (j + 1) heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          T3.publicHash (topNodeInput heap (n + 1) l r) >>= fun a' =>
            neTrialTail (j + 1) heap l r fuel (n + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a') := by
        rw [neTrialTail.eq_2, if_neg hz, ne_topNonceSearch_eq, ne_topNodeHashN_bind]
      rw [e]
      refine (TBSim.steps (s1.trans (s2.trans s3)) (ne_tb_publicHash_bind (fetch_n43238 (im := im) u3 p3) h5 hv hq
        (W := 1 + (22 * fuel + 20)) (fun a' => ?_))).mono (by rw [ne_topNodeInput_blocks] <;> omega)
        (fun _ _ h => h)
      have hwf := Frame.writeHash u3 a' NOUT x12_3 (by decide)
      obtain ⟨w, s4, p4, r4, f4⟩ := nJ_spec (im := im) (writeHash u3 a') (by rw [pc_writeHash, p3, pcOf_add4])
      refine TBSim.steps s4 (ih (n + 1) a' w ⟨p4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by omega))
      · have hw0 : RegsExcept u3 (writeHash u3 a') [] := fun r _ => getReg_writeHash u3 a' r
        exact ((r03.trans hw0).trans r4).mono (by decide)
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x31]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x17]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x29]
      · rw [f4.get (by decide) (fun h => h), hwf.get (by decide) (by simp only [NODE, NOUT]; omega), m32_3, x30_2]
      · exact ((f03.trans hwf).trans f4).mono (fun X _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact Or.inr h
          · exact h.elim)
      · exact (ne_out_after_hash u3 a' heap x12_3).frame f4 (by simp only [NOUT]; omega) (fun h => h) (fun h => h)

/-- The nonce routine after the trial-0 node hash (answer `a`), up to 1076. -/
theorem nonce_run (hpc : t2.pc = pcOf 1138) (a : BitVec 256) :
    TBSim im sk (writeHash t2 a) (32 + (22 * (topNonceCap (j + 1) - 1) + 20))
      (neTrialTail (j + 1) heap l r (topNonceCap (j + 1) - 1) 0 (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => NPost t2 heap leaf j P M res w) := by
  have hj := F.hj
  have hcap := ne_topNonceCap_le (j + 1) (by omega) (by omega)
  have p0 : (writeHash t2 a).pc = pcOf 1139 := by rw [pc_writeHash, hpc, pcOf_add4]
  have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
  have fw := Frame.writeHash t2 a NOUT F.x12 (by decide)
  obtain ⟨u, su, pu, x31, x17, x29, ru, fu⟩ := nsetup_spec (im := im) (writeHash t2 a) p0 j leaf hj F.hl
    (by rw [getReg_writeHash]; exact F.x15) (by rw [getReg_writeHash]; exact F.x20)
    (by rw [getReg_writeHash]; exact F.x18)
  have hst : NTrialSt t2 (j + 1) heap 0 a u := by
    refine ⟨pu, (hw0.trans ru).mono (by decide), x31, x17, by rw [x29, F.hpar], ?_, ?_, ?_⟩
    · rw [fu.get (by decide) (fun h => h), fw.get (by decide) (by simp only [NODE, NOUT]; omega), F.w32] <;> rfl
    · exact (fw.trans fu).mono (fun X _ h => by
        rcases h with h | h
        · exact Or.inr h
        · exact h.elim)
    · exact (ne_out_after_hash t2 a heap F.x12).frame fu (by simp only [NOUT]; omega) (fun h => h) (fun h => h)
  refine (TBSim.steps su (n_trial_loop sk F (topNonceCap (j + 1) - 1) 0 a u hst (by omega))).mono
    (by have := nsetupK_le (j + 1); omega) (fun _ _ h => h)

end loop
end run
end SigGolfCandidate.T3M.Expand.SharedRecover
end
