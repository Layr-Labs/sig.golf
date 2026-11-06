import SigGolfCandidate.SimCore
import SigGolfCandidate.Merge048
import SigGolfCandidate.Merge046
import SigGolfCandidate.FtsTramp
set_option linter.all false

/-! # FTS carrier grind: the expand first-nonce search (`SEARCH`, 61000..61046) behind a trampoline

A trampoline at word `b` (`trampWords b SEARCH ret`) saves `a6`, calls `SEARCH` with `jal a6`, restores `a6` and
jumps to `ret`. `SEARCH` takes `r = s0 >> 13` (the coordinate's FTS frame base `s0` picks the width
`b = 2 - r`), hashes the 64-byte trial block at `a0` into `SCR` for nonces `0, 1, ..` (nonce pad at `a0 + 32`),
stops at the first answer whose kept low half has its top `b` bits 0 (or after nonce `128 * 2^b - 1`), copies the
answer from `SCR` to the real destination `a2`, clears `SCR`, records (witness pad address `a0 + WADJ`, nonce)
at `slotA s0`, and restores every register. `tramp_search` shows the round trip refines `groundFold`. -/

namespace SigGolfCandidate.FtsGrind
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash nonceBytes pad64)
open SphincsSecurity (bytesLE bytesLE_length)

attribute [local rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat

/-- Witness pad address minus the FTS frame block (1384 under E4's witness relayout). -/
def WADJ : Nat := 1384
/-- Zero bits demanded by `SEARCH` for the coordinate with FTS frame base `s0`. -/
def widthOf (s0 : Nat) : Nat := 2 - s0 / 2 ^ 13
/-- Cycles of one trampoline round trip into `SEARCH`. -/
def W_SEARCH (b : Nat) : Nat := 19 * FUEL b + 57

/-! ## `SEARCH` blocks -/

/-- `SEARCH` slice `[a, b)` (word indices). -/
def sl (a b : Nat) : List (BitVec 32) := (searchWords.drop (a - SEARCH)).take (b - a)
def cfgS : Config := { noAlias := true }

sym_block gH0 := symRun cfgS (sl 61000 61008) (pcOf 61000) 20
sym_block gL := symRun cfgS (sl 61008 61011) (pcOf 61008) 20
sym_block gC := symRun cfgS (sl 61011 61015) (pcOf 61011) 20
sym_block gN := symRun cfgS (sl 61015 61018) (pcOf 61015) 20
sym_block gJ := symRun cfgS (sl 61018 61020) (pcOf 61018) 20
sym_block gF := symRun cfgS (sl 61020 61047) (pcOf 61020) 40

theorem code_sl {im : Image} (hS : CodeAt im (pcOf SEARCH) searchWords) (a b : Nat) (ha : SEARCH ≤ a)
    (hb : b ≤ SEARCH + 47) (hab : a ≤ b) : CodeAt im (pcOf a) (sl a b) := by
  have := codeAt_sub (a - SEARCH) hS (seg := sl a b) (by simp [sl, searchWords_length]; omega) (by simp [sl])
  rwa [show SEARCH + (a - SEARCH) = a by omega] at this

/-- The width test: `(x >> 62) >> r = 0` iff `x < 2^(62 + r)`. -/
theorem shr_shr_eq_zero (x : Word) (r : Nat) (hr : r < 64) :
    x >>> 62 >>> ((BitVec.ofNat 64 r).toNat % 64) = 0#64 ↔ x.toNat < 2 ^ (62 + r) := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt hr]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      BitVec.toNat_zero, Nat.div_eq_zero_iff] at this
    rcases this with h | h
    · exact absurd h (by positivity)
    · exact h
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add,
      BitVec.toNat_zero]
    exact Nat.div_eq_of_lt h

section blocks
variable {im : Image} (hS : CodeAt im (pcOf SEARCH) searchWords) (s : MachineState)
include hS

/-- 61000..61007: save `a4 a7 t4 t6`, `a4 := a2`, `a2 := SCR`, `t6 := s0 >> 13`, `a7 := 0`. -/
theorem h0_spec (hpc : s.pc = pcOf 61000) (S0 : Nat) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (hS0 : S0 < 2 ^ 64) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf 61008 ∧
      t.getReg .x12 = BitVec.ofNat 64 SCR ∧ t.getReg .x14 = s.getReg .x12 ∧ t.getReg .x17 = 0 ∧
      t.getReg .x31 = BitVec.ofNat 64 (S0 / 2 ^ 13) ∧ RegsExcept s t [.x12, .x14, .x17, .x31] ∧
      t.getMem (BitVec.ofNat 64 1104) = s.getReg .x14 ∧ t.getMem (BitVec.ofNat 64 1112) = s.getReg .x17 ∧
      t.getMem (BitVec.ofNat 64 1120) = s.getReg .x29 ∧ t.getMem (BitVec.ofNat 64 1128) = s.getReg .x31 ∧
      Frame s t (fun X => 1104 ≤ X ∧ X < 1136) := by
  have hc := code_sl hS 61000 61008 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gH0 hc s hpc (by simp [gH0.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [gH0.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gH0.res]; t3n [SCR]
  · simp only [Result.toState_getReg, gH0.res]; t3n []
  · simp only [Result.toState_getReg, gH0.res]; t3n []
  · simp only [Result.toState_getReg, gH0.res]; t3n [h8]
    rw [ofNat_shr _ _ hS0]; rfl
  · intro r hr; simp at hr; cases r <;> simp_all [gH0.res, rv_simp] <;> rfl
  all_goals try (simp only [Result.toState_getMem, gH0.res]; t3n []; done)
  · intro A hA hn
    simp only [Result.toState_getMem, gH0.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- 61008..61010: pad `a0+32 := a7`, `a0+40 := 0`, then the `ecall`. -/
theorem l_spec (hpc : s.pc = pcOf 61008) (A : Nat) (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (hA : A % 8 = 0)
    (hA' : A + 64 ≤ 2 ^ 24) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 61010 ∧ RegsExcept s t [] ∧
      t.getMem (BitVec.ofNat 64 (A + 32)) = s.getReg .x17 ∧ t.getMem (BitVec.ofNat 64 (A + 40)) = 0 ∧
      Frame s t (fun X => X = A + 32 ∨ X = A + 40) ∧ fetch im t = some (.base .ECALL) := by
  have hc := code_sl hS 61008 61011 (by decide) (by decide) (by decide)
  have hob : gL.res.obligs s := by simp only [gL.res]; t3n [h10]; omega
  refine ⟨_, symRun_sound gL hc s hpc hob, ?_, ?_, ?_, ?_, ?_, symRun_ecall gL hc s hob rfl⟩
  · simp [gL.res, Result.toState_pc, E.eval]
  · intro r _; cases r <;> simp [gL.res, rv_simp] <;> rfl
  · simp only [Result.toState_getMem, gL.res]; t3n [h10]; rw [if_neg (by omega)]
  · simp only [Result.toState_getMem, gL.res]; t3n [h10]
  · intro X hX hn; simp only [Result.toState_getMem, gL.res]; t3n [h10]
    rw [if_neg (by omega), if_neg (by omega)]

/-- 61011..61014: the width test on the top word of the kept low half at `SCR + 8`. -/
theorem c_spec (hpc : s.pc = pcOf 61011) (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) (r : Nat)
    (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps im s 4 4 t ∧
      t.pc = (if (s.getMem (BitVec.ofNat 64 (SCR + 8))).toNat < 2 ^ (62 + r) then pcOf 61020 else pcOf 61015) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl hS 61011 61015 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gC hc s hpc (by simp only [gC.res]; t3n [h12, SCR]; norm_num), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gC.res, rv_simp, h12, h31, SCR, ofNat_add_ofNat, beq_iff_eq]
    have e62 : ((62#64 : Word).toNat % 64) = 62 := rfl
    simp only [e62]
    have hiff := shr_shr_eq_zero (s.getMem (BitVec.ofNat 64 (8257536 + 8))) r (by omega)
    by_cases h1 : s.getMem (BitVec.ofNat 64 (8257536 + 8)) >>> 62 >>> ((BitVec.ofNat 64 r).toNat % 64) = 0#64
    · rw [if_pos h1]; exact (if_pos (hiff.mp h1)).symm
    · rw [if_neg h1]; exact (if_neg (fun h => h1 (hiff.mpr h))).symm
  · intro r hr; simp at hr; cases r <;> simp_all [gC.res, rv_simp] <;> rfl
  · intro A _ _; simp [gC.res, rv_simp]

/-- 61015..61017: stop after nonce `511 >> r`. -/
theorem n_spec (hpc : s.pc = pcOf 61015) (r : Nat) (h31 : s.getReg .x31 = BitVec.ofNat 64 r) (hr : r < 2) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if s.getReg .x17 = BitVec.ofNat 64 (511 / 2 ^ r) then pcOf 61020 else pcOf 61018) ∧
      RegsExcept s t [.x29] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl hS 61015 61018 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gN hc s hpc (by simp [gN.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, gN.res, rv_simp, h31, beq_iff_eq]
    rw [show (511#64 : Word) = BitVec.ofNat 64 511 from rfl, ofNat_shr' 511 r]
    rw [show r % 2 ^ 64 % 64 = r by omega, show 511 % 2 ^ 64 = 511 from rfl]
  · intro r hr; simp at hr; cases r <;> simp_all [gN.res, rv_simp] <;> rfl
  · intro A _ _; simp [gN.res, rv_simp]

/-- 61018..61019: next nonce, back to 61008. -/
theorem j_spec (hpc : s.pc = pcOf 61018) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 61008 ∧ t.getReg .x17 = s.getReg .x17 + 1#64 ∧
      RegsExcept s t [.x17] ∧ Frame s t (fun _ => False) := by
  have hc := code_sl hS 61018 61020 (by decide) (by decide) (by decide)
  refine ⟨_, symRun_sound gJ hc s hpc (by simp [gJ.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [gJ.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, gJ.res]; simp [rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [gJ.res, rv_simp] <;> rfl
  · intro A _ _; simp [gJ.res, rv_simp]

set_option maxHeartbeats 1000000 in
/-- 61020..61046: copy the answer `SCR -> D`, clear `SCR`, record at `slotA s0`, `a2 := a4`, restore and clear
the saves, return through `a6`. -/
theorem f_spec (hpc : s.pc = pcOf 61020) (A D S0 R : Nat)
    (h10 : s.getReg .x10 = BitVec.ofNat 64 A) (h14 : s.getReg .x14 = BitVec.ofNat 64 D)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 SCR) (h8 : s.getReg .x8 = BitVec.ofNat 64 S0)
    (h16 : s.getReg .x16 = pcOf R) (hA : A < 2 ^ 24) (hD : D % 8 = 0) (hD1 : 1136 ≤ D) (hD2 : D + 32 ≤ SCR)
    (hS0 : S0 % 8 = 0) (hS1 : 16 ≤ S0) (hS2 : S0 < 2 ^ 14) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf R ∧
      t.getReg .x12 = BitVec.ofNat 64 D ∧ t.getReg .x14 = s.getMem (BitVec.ofNat 64 1104) ∧
      t.getReg .x17 = s.getMem (BitVec.ofNat 64 1112) ∧ t.getReg .x29 = s.getMem (BitVec.ofNat 64 1120) ∧
      t.getReg .x31 = s.getMem (BitVec.ofNat 64 1128) ∧ RegsExcept s t [.x12, .x14, .x17, .x29, .x31] ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = s.getMem (BitVec.ofNat 64 (SCR + 8 * k))) ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0) ∧
      t.getMem (BitVec.ofNat 64 (slotA S0)) = BitVec.ofNat 64 (A + WADJ) ∧
      t.getMem (BitVec.ofNat 64 (slotA S0 + 8)) = s.getReg .x17 ∧
      (∀ k < 4, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0) ∧
      Frame s t (fun X => (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ (SCR ≤ X ∧ X < SCR + 32) ∨
        (slotA S0 ≤ X ∧ X < slotA S0 + 16) ∨ (1104 ≤ X ∧ X < 1136)) := by
  have hc := code_sl hS 61020 61047 (by decide) (by decide) (by decide)
  simp only [SCR, slotA, WADJ] at h12 hD2 ⊢
  have hob : gF.res.obligs s := by
    simp only [gF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [Nat.mod_eq_of_lt, not_false_eq_true, and_true, true_and]
    and_intros <;> omega
  refine ⟨_, symRun_sound gF hc s hpc hob, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear hob
  · simp only [Result.toState_pc, gF.res]; t3n [h16, pcOf_and_max]
  · simp only [Result.toState_getReg, gF.res]; t3n [h14]
  · simp only [Result.toState_getReg, gF.res]; t3n []
  · simp only [Result.toState_getReg, gF.res]; t3n []
  · simp only [Result.toState_getReg, gF.res]; t3n []
  · simp only [Result.toState_getReg, gF.res]; t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [gF.res, rv_simp] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro k hk
    simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]
  · intro k hk
    simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    interval_cases k <;> simp (disch := omega) only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, if_pos, if_neg, if_true, if_false] <;> rfl
  · intro X hX hn
    simp only [Result.toState_getMem, gF.res]; t3n [h10, h14, h12, h8]
    simp (disch := omega) only [if_pos, if_neg, if_true, if_false]

end blocks

/-! ## The search loop and the trampoline round trip -/

theorem frame_readWordsG {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWordsG h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]

theorem trialInput_length (pre right : List UInt8) (n : Nat) (hp : pre.length = 32) (hr : right.length = 16) :
    (trialInput pre n right).length = 64 := by
  simp [trialInput, nonceBytes, bytesLE_length, hp, hr]

theorem trial_blocks (pre right : List UInt8) (n : Nat) (hp : pre.length = 32) (hr : right.length = 16) :
    (toQ (pad64 (trialInput pre n right))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [trialInput_length _ _ _ hp hr]),
    blocks_toQ ⟨by rw [trialInput_length _ _ _ hp hr]; omega, by rw [trialInput_length _ _ _ hp hr]⟩,
    trialInput_length _ _ _ hp hr]

/-- The kept low half has its top `b` bits zero iff its top word is below `2^(64 - b)`. -/
theorem zeroOk_iff (a : HashOutput) (r : Nat) (hr : r < 2) :
    zeroOk (2 - r) a = true ↔ (a.extractLsb' 64 64).toNat < 2 ^ (62 + r) := by
  unfold zeroOk
  rw [decide_eq_true_iff, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    Nat.shiftRight_eq_div_pow]
  have e : a.toNat / 2 ^ 64 % 2 ^ 64 = a.toNat % 2 ^ 128 / 2 ^ 64 := by
    rw [show (2 : Nat) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, Nat.mod_mul_right_div_self]
  rw [e, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add,
    show 62 + r + 64 = 128 - (2 - r) by omega]

theorem fuel_eq (S0 : Nat) (h : S0 < 2 ^ 14) : FUEL (widthOf S0) = 511 / 2 ^ (S0 / 2 ^ 13) := by
  have : S0 / 2 ^ 13 = 0 ∨ S0 / 2 ^ 13 = 1 := by omega
  unfold FUEL widthOf; rcases this with h | h <;> rw [h] <;> rfl

theorem width_eq (S0 : Nat) : widthOf S0 = 2 - S0 / 2 ^ 13 := rfl

/-- What follows the trial-`n` hash in `search` (fuel = trials left). -/
def sTail (b : Nat) (pre right : List UInt8) : Nat → Nat → HashOutput → M (Nat × HashOutput)
  | 0, n, a => pure (n, a)
  | fuel + 1, n, a => if zeroOk b a then pure (n, a) else search b pre right fuel (n + 1)

theorem search_eq (b : Nat) (pre right : List UInt8) (fuel n : Nat) :
    search b pre right fuel n = publicHash (trialInput pre n right) >>= sTail b pre right fuel n := by
  cases fuel <;> rfl

/-- A trampoline call at word `b` returning to `ret`: the trial block at `A` holds `pre` (32 bytes), any pad, and
`right` (16 bytes); the answer goes to `D` (which may overlap the block); the FTS frame base is `S0`. -/
structure SearchIn (b ret A D S0 : Nat) (pre right : List UInt8) (s : MachineState) : Prop where
  pc : s.pc = pcOf b
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 S0
  x10 : s.getReg .x10 = BitVec.ofNat 64 A
  x11 : s.getReg .x11 = BitVec.ofNat 64 64
  x12 : s.getReg .x12 = BitVec.ofNat 64 D
  lpre : pre.length = 32
  lright : right.length = 16
  mpre : s.readWords (BitVec.ofNat 64 A) 4 = wordsOf pre
  mright : s.readWords (BitVec.ofNat 64 (A + 48)) 2 = wordsOf right
  hA : A % 8 = 0
  hA1 : 1144 ≤ A
  hA2 : A + 64 ≤ SCR
  hD : D % 8 = 0
  hD1 : 1144 ≤ D
  hD2 : D + 32 ≤ SCR
  hS0 : S0 % 8 = 0
  hS1 : 16 ≤ S0
  hS2 : S0 < 2 ^ 14
  hb : b + 5 < 2 ^ 18
  hret : ret < 2 ^ 18

/-- Words a `SEARCH` call may write (all but `D`, the pad and the record are zero again on return). -/
def SearchW (A D S0 : Nat) (X : Nat) : Prop :=
  (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) ∨ X = A + 32 ∨ X = A + 40 ∨ (slotA S0 ≤ X ∧ X < slotA S0 + 16) ∨
    (1104 ≤ X ∧ X < 1144) ∨ (SCR ≤ X ∧ X < SCR + 32)

/-- Back at `ret` with the answer of the ground fold at `D`. -/
structure SearchOut (s : MachineState) (ret A D S0 : Nat) (res : Nat × HashOutput) (t : MachineState) : Prop where
  pc : t.pc = pcOf ret
  regs : RegsExcept s t []
  ans : ∀ k < 4, t.getMem (BitVec.ofNat 64 (D + 8 * k)) = res.2.extractLsb' (64 * k) 64
  nle : res.1 ≤ FUEL (widthOf S0)
  pad32 : ¬ (D ≤ A + 32 ∧ A + 32 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 res.1
  pad40 : ¬ (D ≤ A + 40 ∧ A + 40 < D + 32) → t.getMem (BitVec.ofNat 64 (A + 40)) = 0
  slot0 : t.getMem (BitVec.ofNat 64 (slotA S0)) = BitVec.ofNat 64 (A + WADJ)
  slot1 : t.getMem (BitVec.ofNat 64 (slotA S0 + 8)) = BitVec.ofNat 64 res.1
  saves : ∀ k < 5, t.getMem (BitVec.ofNat 64 (1104 + 8 * k)) = 0
  scr : ∀ k < 4, t.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = 0
  frame : Frame s t (SearchW A D S0)

/-- Loop words: the pad, the saves and `SCR`. -/
def LoopW (A : Nat) (X : Nat) : Prop := X = A + 32 ∨ X = A + 40 ∨ (1104 ≤ X ∧ X < 1144) ∨ (SCR ≤ X ∧ X < SCR + 32)

def loopRegs : List Reg := [.x12, .x14, .x16, .x17, .x29, .x31]

/-- At word `pcw` of `SEARCH`, after the entry, with nonce `n`. -/
structure AtS (s : MachineState) (b A D S0 pcw n : Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf pcw
  regs : RegsExcept s u loopRegs
  x12 : u.getReg .x12 = BitVec.ofNat 64 SCR
  x14 : u.getReg .x14 = BitVec.ofNat 64 D
  x16 : u.getReg .x16 = pcOf (b + 2)
  x17 : u.getReg .x17 = BitVec.ofNat 64 n
  x31 : u.getReg .x31 = BitVec.ofNat 64 (S0 / 2 ^ 13)
  sv0 : u.getMem (BitVec.ofNat 64 1104) = s.getReg .x14
  sv1 : u.getMem (BitVec.ofNat 64 1112) = s.getReg .x17
  sv2 : u.getMem (BitVec.ofNat 64 1120) = s.getReg .x29
  sv3 : u.getMem (BitVec.ofNat 64 1128) = s.getReg .x31
  sv4 : u.getMem (BitVec.ofNat 64 1136) = s.getReg .x16
  frame : Frame s u (LoopW A)
  hn : n ≤ FUEL (widthOf S0)

/-- After the trial-`n` hash (answer `a` in `SCR`, pad `n ‖ 0`). -/
structure Hashed (u : MachineState) (A n : Nat) (a : HashOutput) : Prop where
  scr : ∀ k < 4, u.getMem (BitVec.ofNat 64 (SCR + 8 * k)) = a.extractLsb' (64 * k) 64
  p32 : u.getMem (BitVec.ofNat 64 (A + 32)) = BitVec.ofNat 64 n
  p40 : u.getMem (BitVec.ofNat 64 (A + 40)) = 0

section run
variable {im : Image} {sk : BitVec 256} {b ret A D S0 : Nat} {pre right : List UInt8} {s : MachineState}
  (hS : CodeAt im (pcOf SEARCH) searchWords) (hT : CodeAt im (pcOf b) (trampWords b SEARCH ret))
  (F : SearchIn b ret A D S0 pre right s)
include hS hT F

/-- The exit 61020 -> `ret`: copy, clear, record, restore; then the trampoline tail. -/
theorem exit_spec {n : Nat} {a : HashOutput} {v : MachineState} (hv : AtS s b A D S0 61020 n v)
    (hh : Hashed v A n a) : TBSim im sk v 30 (pure (n, a)) (SearchOut s ret A D S0) := by
  have hb := F.hb; have hret := F.hret; have hA1 := F.hA1; have hA2 := F.hA2; have hD1 := F.hD1
  have hD2 := F.hD2; have hS1 := F.hS1; have hS2 := F.hS2
  simp only [SCR] at hA2 hD2
  obtain ⟨t1, s1, p1, x12, x14, x17, x29, x31, r1, ans, scr, sl0, sl1, sv, f1⟩ :=
    f_spec hS v hv.pc A D S0 (b + 2) (by rw [hv.regs.get (by decide)]; exact F.x10) hv.x14 hv.x12
      (by rw [hv.regs.get (by decide)]; exact F.x8) hv.x16 (by omega) F.hD (by omega) (by simp only [SCR]; omega)
      F.hS0 F.hS1 F.hS2
  obtain ⟨t2, s2, p2, x16, r2, m2, f2⟩ := tramp_tail hT hb hret t1 p1
  have g1136 : t1.getMem (BitVec.ofNat 64 1136) = s.getReg .x16 := by
    rw [f1.get (by decide) (by simp only [SCR, slotA]; omega), hv.sv4]
  have t2m : ∀ X, X < 2 ^ 64 → X ≠ 1136 → t2.getMem (BitVec.ofNat 64 X) = t1.getMem (BitVec.ofNat 64 X) :=
    fun X hX h => f2.get hX h
  have t1m : ∀ X, X < 2 ^ 64 → ¬ (X = D ∨ X = D + 8 ∨ X = D + 16 ∨ X = D + 24) → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      ¬ (slotA S0 ≤ X ∧ X < slotA S0 + 16) → ¬ (1104 ≤ X ∧ X < 1136) →
      t1.getMem (BitVec.ofNat 64 X) = v.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 h3 h4 =>
    f1.get hX (by rintro (h | h | h | h) <;> contradiction)
  refine tb_pure_steps (s1.trans s2) ⟨p2, ?_, ?_, hv.hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _
    by_cases h16 : r = .x16
    · subst h16; rw [x16, g1136]
    rw [r2.get (by simpa using h16)]
    by_cases hr : r ∈ [Reg.x12, .x14, .x17, .x29, .x31]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · rw [x12, F.x12]
      · rw [x14, hv.sv0]
      · rw [x17, hv.sv1]
      · rw [x29, hv.sv2]
      · rw [x31, hv.sv3]
    · have hr' : r ∉ loopRegs := by
        simp only [loopRegs, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; tauto
      rw [r1.get hr, hv.regs.get hr']
  · intro k hk
    rw [t2m _ (by omega) (by omega), ans k hk, hh.scr k hk]
  · intro h
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR]; omega)
      (by simp only [slotA, SCR]; omega) (by omega), hh.p32]
  · intro h
    rw [t2m _ (by omega) (by omega), t1m _ (by omega) (by omega) (by simp only [SCR]; omega)
      (by simp only [slotA, SCR]; omega) (by omega), hh.p40]
  · rw [t2m _ (by simp only [slotA, SCR]; omega) (by simp only [slotA, SCR]; omega), sl0]
  · rw [t2m _ (by simp only [slotA, SCR]; omega) (by simp only [slotA, SCR]; omega), sl1, hv.x17]
  · intro k hk
    by_cases h4 : k = 4
    · subst h4; exact m2
    · rw [t2m _ (by omega) (by omega), sv k (by omega)]
  · intro k hk
    rw [t2m _ (by simp only [SCR]; omega) (by simp only [SCR]; omega), scr k hk]
  · refine ((hv.frame.trans f1).trans f2).mono (fun X _ h => ?_)
    unfold SearchW
    unfold LoopW at h
    rcases h with ((h | h | h | h) | (h | h | h | h)) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))

omit hS hT F in
theorem AtS.move {pcw pcw' n n' : Nat} {u w : MachineState} (h : AtS s b A D S0 pcw n u) (hpc : w.pc = pcOf pcw')
    (hr : RegsExcept u w [.x17, .x29]) (hf : Frame u w (fun _ => False)) (h17 : w.getReg .x17 = BitVec.ofNat 64 n')
    (hn : n' ≤ FUEL (widthOf S0)) : AtS s b A D S0 pcw' n' w where
  pc := hpc
  regs := (h.regs.trans hr).mono (by decide)
  x12 := by rw [hr.get (by decide)]; exact h.x12
  x14 := by rw [hr.get (by decide)]; exact h.x14
  x16 := by rw [hr.get (by decide)]; exact h.x16
  x17 := h17
  x31 := by rw [hr.get (by decide)]; exact h.x31
  sv0 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv0
  sv1 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv1
  sv2 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv2
  sv3 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv3
  sv4 := by rw [hf.get (by decide) (fun h => h)]; exact h.sv4
  frame := (h.frame.trans hf).mono (fun _ _ h => by rcases h with h | h; exact h; exact h.elim)
  hn := hn

omit hS hT F in
theorem Hashed.move {n : Nat} {a : HashOutput} {u w : MachineState} (h : Hashed u A n a)
    (hf : Frame u w (fun _ => False)) (hA : A + 64 ≤ 2 ^ 24) : Hashed w A n a where
  scr k hk := by rw [hf.get (by simp only [SCR]; omega) (fun h => h)]; exact h.scr k hk
  p32 := by rw [hf.get (by omega) (fun h => h)]; exact h.p32
  p40 := by rw [hf.get (by omega) (fun h => h)]; exact h.p40

/-- One trial: pad `n ‖ 0`, then the hash of the trial block into `SCR`. -/
theorem trial_spec {β : Type} {n : Nat} {u : MachineState} (hu : AtS s b A D S0 61008 n u) {W : Nat}
    {f : HashOutput → M β} {Q : β → MachineState → Prop}
    (h : ∀ a w, AtS s b A D S0 61011 n w → Hashed w A n a → TBSim im sk w W (f a) Q) :
    TBSim im sk u (2 + (8 + W)) (publicHash (trialInput pre n right) >>= f) Q := by
  have hA := F.hA; have hA1 := F.hA1; have hA2 := F.hA2; have hS2 := F.hS2
  simp only [SCR] at hA2
  have hnF : n < 2 ^ 64 := by
    have h1 := hu.hn
    rw [fuel_eq S0 hS2] at h1
    have := Nat.div_le_self 511 (2 ^ (S0 / 2 ^ 13))
    omega
  have g10 : u.getReg .x10 = BitVec.ofNat 64 A := by rw [hu.regs.get (by decide)]; exact F.x10
  obtain ⟨u1, s1, p1, r1, m32, m40, f1, fe1⟩ := l_spec hS u hu.pc A g10 hA (by omega)
  rw [hu.x17] at m32
  have fs1 : Frame s u1 (LoopW A) := (hu.frame.trans f1).mono (fun X _ h => by
    rcases h with h | h | h
    · exact h
    · exact Or.inl h
    · exact Or.inr (Or.inl h))
  have g1 : ∀ x, x ∉ loopRegs → u1.getReg x = s.getReg x := fun x hx => by
    rw [r1.get (by simp), hu.regs.get hx]
  have h12 : u1.getReg .x12 = BitVec.ofNat 64 SCR := by rw [r1.get (by simp)]; exact hu.x12
  have hl := trialInput_length pre right n F.lpre F.lright
  have hq : hashInput u1 = toQ (pad64 (trialInput pre n right)) := by
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u1 _ 0 A hl (by rw [g1 _ (by decide)]; exact F.x10) hA (by omega)
      (by rw [g1 _ (by decide)]; exact F.x11) (by norm_num) ?_
    rw [show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_add, readWords_add,
      frame_readWordsG fs1 A 4 (by omega) (fun i hi => by unfold LoopW; simp only [SCR]; omega),
      show A + 8 * 4 = A + 32 by ring, readWords_two, m32, m40, show A + 32 + 8 * 2 = A + 48 by ring,
      frame_readWordsG fs1 (A + 48) 2 (by omega) (fun i hi => by unfold LoopW; simp only [SCR]; omega),
      F.mpre, F.mright, trialInput, wordsOf_append _ _ (by rw [List.length_append, F.lpre]; simp [nonceBytes,
        bytesLE_length]), wordsOf_append _ _ (by rw [F.lpre]), nonce_words n hnF]
  have hv : hashArgumentsValid u1 = true := hashArgs_const u1 A 64 SCR (by rw [g1 _ (by decide)]; exact F.x10)
    (by rw [g1 _ (by decide)]; exact F.x11) h12 hA (by norm_num) (by omega) (by decide) (by decide)
  have h5 : u1.getReg .x5 = 0 := by rw [g1 _ (by decide)]; exact F.x5
  have e := tb_pub (sk := sk) (W := W) (f := f) (Q := Q) fe1 h5 hv hq (fun a => ?_)
  · have := TBSim.steps s1 e
    rwa [trial_blocks pre right n F.lpre F.lright] at this
  have hwf := Frame.writeHash u1 a SCR h12 (by decide)
  have fw : Frame s (writeHash u1 a) (LoopW A) := (fs1.trans hwf).mono (fun X _ h => by
    rcases h with h | h
    · exact h
    · exact Or.inr (Or.inr (Or.inr h)))
  have keep : ∀ X, X < 2 ^ 64 → ¬ (SCR ≤ X ∧ X < SCR + 32) →
      (writeHash u1 a).getMem (BitVec.ofNat 64 X) = u1.getMem (BitVec.ofNat 64 X) := fun X hX h => hwf.get hX h
  have keepu : ∀ X, X < 2 ^ 64 → X ≠ A + 32 → X ≠ A + 40 →
      u1.getMem (BitVec.ofNat 64 X) = u.getMem (BitVec.ofNat 64 X) := fun X hX h1 h2 =>
    f1.get hX (by rintro (h | h) <;> contradiction)
  refine h a (writeHash u1 a) ⟨by rw [pc_writeHash, p1, pcOf_add4], fun x hx => by rw [getReg_writeHash, g1 x hx],
    by rw [getReg_writeHash]; exact h12, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x14,
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x16, by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x17,
    by rw [getReg_writeHash, r1.get (by simp)]; exact hu.x31,
    by rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv0,
    by rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv1,
    by rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv2,
    by rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv3,
    by rw [keep _ (by decide) (by simp only [SCR]; omega), keepu _ (by decide) (by omega) (by omega)]; exact hu.sv4,
    fw, hu.hn⟩ ⟨fun k hk => ?_, by rw [keep _ (by omega) (by simp only [SCR]; omega)]; exact m32,
      by rw [keep _ (by omega) (by simp only [SCR]; omega)]; exact m40⟩
  rw [getMem_writeHash u1 a SCR _ h12 (by decide) (by simp only [SCR]; omega)]
  interval_cases k <;> simp

/-- The search loop from 61008 with nonce `n` and `fuel` trials after this one. -/
theorem loop_spec : ∀ fuel n u, AtS s b A D S0 61008 n u → n + fuel = FUEL (widthOf S0) →
    TBSim im sk u (19 * fuel + 47) (search (widthOf S0) pre right fuel n) (SearchOut s ret A D S0) := by
  have hS2 := F.hS2
  have hr : S0 / 2 ^ 13 < 2 := by omega
  have hF := fuel_eq S0 hS2
  have hFl : FUEL (widthOf S0) < 2 ^ 64 := by rw [hF]; exact lt_of_le_of_lt (Nat.div_le_self _ _) (by norm_num)
  -- the zero test at 61011
  have test : ∀ n a w, AtS s b A D S0 61011 n w → Hashed w A n a → ∃ w1, Steps im w 4 4 w1 ∧
      AtS s b A D S0 (if zeroOk (widthOf S0) a = true then 61020 else 61015) n w1 ∧ Hashed w1 A n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := c_spec hS w hw.pc hw.x12 _ hw.x31 hr
    have e : (w.getMem (BitVec.ofNat 64 (SCR + 8))).toNat < 2 ^ (62 + S0 / 2 ^ 13) ↔
        zeroOk (widthOf S0) a = true := by
      rw [width_eq, zeroOk_iff a _ hr]
      have := hh.scr 1 (by decide)
      simp only [Nat.mul_one] at this
      rw [this]
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move f1 (by have := F.hA2; simp only [SCR] at this; omega)⟩
    rw [p1]; by_cases hz : zeroOk (widthOf S0) a = true
    · rw [if_pos (e.mpr hz), if_pos hz]
    · rw [if_neg (fun h => hz (e.mp h)), if_neg hz]
  -- the cap test at 61015
  have capT : ∀ n a w, AtS s b A D S0 61015 n w → Hashed w A n a → ∃ w1, Steps im w 3 3 w1 ∧
      AtS s b A D S0 (if n = FUEL (widthOf S0) then 61020 else 61018) n w1 ∧ Hashed w1 A n a := by
    intro n a w hw hh
    obtain ⟨w1, s1, p1, r1, f1⟩ := n_spec hS w hw.pc _ hw.x31 hr
    refine ⟨w1, s1, hw.move ?_ (r1.mono (by decide)) f1 (by rw [r1.get (by decide)]; exact hw.x17) hw.hn,
      hh.move f1 (by have := F.hA2; simp only [SCR] at this; omega)⟩
    have hnl : n < 2 ^ 64 := by have := hw.hn; omega
    rw [p1, hw.x17]
    by_cases hz : n = FUEL (widthOf S0)
    · rw [if_pos (by rw [hz, hF]), if_pos hz]
    · rw [if_neg (fun h => hz ((ofNat_inj hnl hFl).mp (h.trans (congrArg _ hF.symm)))), if_neg hz]
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hn
    simp only [Nat.add_zero] at hn
    rw [search_eq]
    refine (trial_spec hS hT F hu (W := 37) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (widthOf S0) a = true
    · rw [if_pos hz] at hw1
      exact (TBSim.steps s1 (exit_spec hS hT F hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_pos hn] at hw2
      exact TBSim.steps s1 (TBSim.steps s2 (exit_spec hS hT F hw2 hh2))
  | succ fuel ih =>
    intro n u hu hn
    rw [search_eq]
    refine (trial_spec hS hT F hu (W := 19 * fuel + 56) (fun a w hw hh => ?_)).mono (by omega) (fun _ _ h => h)
    obtain ⟨w1, s1, hw1, hh1⟩ := test n a w hw hh
    by_cases hz : zeroOk (widthOf S0) a = true
    · rw [if_pos hz] at hw1
      simp only [sTail, hz, if_true]
      exact (TBSim.steps s1 (exit_spec hS hT F hw1 hh1)).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at hw1
      simp only [sTail, hz, Bool.false_eq_true, if_false]
      obtain ⟨w2, s2, hw2, hh2⟩ := capT n a w1 hw1 hh1
      rw [if_neg (by omega)] at hw2
      obtain ⟨w3, s3, p3, x17, r3, f3⟩ := j_spec hS w2 hw2.pc
      have hw3 : AtS s b A D S0 61008 (n + 1) w3 := hw2.move p3 (r3.mono (by decide)) f3
        (by rw [x17, hw2.x17, ofNat_add_ofNat]) (by omega)
      have := TBSim.steps s1 (TBSim.steps s2 (TBSim.steps s3 (ih (n + 1) w3 hw3 (by omega))))
      exact this.mono (by omega) (fun _ _ h => h)

/-- **The trampoline round trip into `SEARCH` refines the ground fold** of width `widthOf S0`. -/
theorem tramp_search : TBSim im sk s (W_SEARCH (widthOf S0)) (groundFold (widthOf S0) pre right)
    (SearchOut s ret A D S0) := by
  have hS2 := F.hS2
  obtain ⟨u0, s0, p0, x16, r0, m0, f0⟩ := tramp_head hT F.hb (by decide) s F.pc
  obtain ⟨u1, s1, p1, x12, x14, x17, x31, r1, sv0, sv1, sv2, sv3, f1⟩ :=
    h0_spec hS u0 p0 S0 (by rw [r0.get (by decide)]; exact F.x8) (by omega)
  have hu1 : AtS s b A D S0 61008 0 u1 :=
    { pc := p1
      regs := (r0.trans r1).mono (by decide)
      x12 := x12
      x14 := by rw [x14, r0.get (by decide)]; exact F.x12
      x16 := by rw [r1.get (by decide)]; exact x16
      x17 := x17
      x31 := x31
      sv0 := by rw [sv0, r0.get (by decide)]
      sv1 := by rw [sv1, r0.get (by decide)]
      sv2 := by rw [sv2, r0.get (by decide)]
      sv3 := by rw [sv3, r0.get (by decide)]
      sv4 := by rw [f1.get (by decide) (by omega)]; exact m0
      frame := (f0.trans f1).mono (fun X _ h => by
        unfold LoopW; rcases h with h | h
        · exact Or.inr (Or.inr (Or.inl (by omega)))
        · exact Or.inr (Or.inr (Or.inl (by omega))))
      hn := Nat.zero_le _ }
  have := TBSim.steps s0 (TBSim.steps s1 (loop_spec (sk := sk) hS hT F (FUEL (widthOf S0)) 0 u1 hu1 (by omega)))
  exact this.mono (by unfold W_SEARCH; omega) (fun _ _ h => h)

end run

end SigGolfCandidate.FtsGrind

