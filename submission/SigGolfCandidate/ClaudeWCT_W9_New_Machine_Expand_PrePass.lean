import SigGolfCandidate.T3M_Expand_Blocks
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePassBits

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
