import SigGolfCandidate.Merge026
import SigGolfCandidate.Merge028
import SigGolfCandidate.Merge033
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge047
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge054
import SigGolfCandidate.Merge055
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge073

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
