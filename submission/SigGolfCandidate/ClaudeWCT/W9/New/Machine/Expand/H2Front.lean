import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsChain
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Sign.FtsRuns
import SigGolfCandidate.T3M.Sign.TopBlocks
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Honest
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack

/-! # H2 expander prologue: the compact signature, un-shifted in place

Word 0 jumps to the prologue (words 42777..42794): it keeps the 14 tail bytes (sig 5296..5311, read as two words;
bytes 5310/5311 are zero), moves sig [2928, 5296) up by 16 bytes (backwards, one word per step), stores the kept
words at sig 2928 (the top sibling with its two omitted bytes zero), clears its scratch registers and jumps to word
1. The machine is then exactly in the old expander's state after word 0, for the full-layout bytes
`sigB (sigDecC b)`. -/

section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (ex_valid ex_ne bytesToWordLE_bytes_e bytes_length_e extractByte_bytesToWordLE_e extractByte_toNat_e word_ext_bytes_e)
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.T3M (sigDig sigDec sigDigests sigDigests_sigDec)
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000

def proCode : List (BitVec 32) :=
  [36535, 1259245203, 963331, 9352067, 36663, 3071217427, 4287532691, 964227, 14596131, 4292831971, 7286819,
    8336419, 787, 915, 3731, 3859, 1683, 3050135663]
def proA : List (BitVec 32) := [36535, 1259245203, 963331, 9352067, 36663, 3071217427]
def proL : List (BitVec 32) := [4287532691, 964227, 14596131, 4292831971]
def proB : List (BitVec 32) := [7286819, 8336419, 787, 915, 3731, 3859, 1683]
def proJ : BitVec 32 := 3050135663
def w0Word : BitVec 32 := 1179816047
def frontTail : List (BitVec 32) := SigGolfCandidate.T3M.Expand.seg_0.drop 1
theorem proCode_eq : proCode = proA ++ proL ++ proB ++ [proJ] := rfl

/-- The prologue and the new word 0 are in the image. -/
def ProAt (im : Image) : Prop := CodeAt im (pcOf 0) [w0Word] ∧ CodeAt im (pcOf 42777) proCode ∧
  CodeAt im (pcOf 1) frontTail

section code
variable {im : Image} (hP : ProAt im)
include hP
theorem codeAt_proA : CodeAt im (pcOf 42777) proA := codeAt_appL (codeAt_appL (codeAt_appL (proCode_eq ▸ hP.2.1)))
theorem codeAt_proL : CodeAt im (pcOf 42783) proL :=
  codeAt_appR (n := 42777) (a := proA) (codeAt_appL (codeAt_appL (proCode_eq ▸ hP.2.1))) (by decide)
theorem codeAt_proB : CodeAt im (pcOf 42787) proB :=
  codeAt_appR (n := 42777) (a := proA ++ proL) (codeAt_appL (proCode_eq ▸ hP.2.1)) (by decide)
theorem codeAt_proJ : CodeAt im (pcOf 42794) [proJ] :=
  codeAt_appR (n := 42777) (a := proA ++ proL ++ proB) (proCode_eq ▸ hP.2.1) (by decide)
end code

sym_block h2_proA := symRun { noAlias := true } proA (pcOf 42777) 50
sym_block h2_proL := symRun { noAlias := true } proL (pcOf 42783) 50
sym_block h2_proB := symRun { noAlias := true } proB (pcOf 42787) 50
sym_block h2_front := symRun { noAlias := true } frontTail (pcOf 1) 200

theorem w0_step {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps im s 1 1 (s.setPC (pcOf 42777)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo w0Word 0 = some 42777 by decide)
  exact jal_x0_step hP.1 hd hoff s hpc

theorem proJ_step {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 42794) :
    Steps im s 1 1 (s.setPC (pcOf 1)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo proJ 42794 = some 1 by decide)
  exact jal_x0_step (codeAt_proJ hP) hd hoff s hpc

theorem proA_spec {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 42777) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42783 ∧
      t.getReg .x29 = BitVec.ofNat 64 0x84b0 ∧ t.getReg .x30 = BitVec.ofNat 64 0x7b70 ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 0x84b0) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 0x84b8) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound h2_proA (codeAt_proA hP) s hpc
    (by simp [h2_proA.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_proA.res, E.eval]
  · simp only [Result.toState_getReg, h2_proA.res]; t3n []
  · simp only [Result.toState_getReg, h2_proA.res]; t3n []
  · simp only [Result.toState_getReg, h2_proA.res]; t3n []
  · simp only [Result.toState_getReg, h2_proA.res]; t3n []
  · ex_regs h2_proA.res
  · intro A _ _; simp [h2_proA.res, rv_simp]

theorem ofNat_sub8 (X : Nat) (hX : 8 ≤ X) (hX' : X < 2 ^ 64) :
    BitVec.ofNat 64 X + BitVec.ofNat 64 (2 ^ 64 - 8) = BitVec.ofNat 64 (X - 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have h16 : 16 ≤ 2 ^ 64 := le_trans (by norm_num : (16 : Nat) ≤ 2 ^ 4) (Nat.pow_le_pow_right (by norm_num) (by norm_num))
  generalize (2 : Nat) ^ 64 = P at *
  rw [Nat.mod_eq_of_lt hX', Nat.mod_eq_of_lt (show P - 8 < P by omega), Nat.mod_eq_of_lt (show X - 8 < P by omega),
    show X + (P - 8) = (X - 8) + P by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (show X - 8 < P by omega)]

theorem m64_add8 (X : Nat) (h : X ≤ 33968) : (X + 8) % 18446744073709551616 = X + 8 :=
  Nat.mod_eq_of_lt (by omega)
theorem m64_sub8 (X : Nat) (hX : 8 ≤ X) (h : X ≤ 33968) :
    (X + 18446744073709551608) % 18446744073709551616 = X - 8 := by
  rw [show X + 18446744073709551608 = (X - 8) + 18446744073709551616 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)
theorem ofNat_m8 (X : Nat) (hX : 8 ≤ X) (h : X ≤ 33968) :
    BitVec.ofNat 64 (X + 18446744073709551608) = BitVec.ofNat 64 (X - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [m64_sub8 X hX h, Nat.mod_eq_of_lt (show X - 8 < 18446744073709551616 by omega)]

theorem proL_spec {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 42783) (X : Nat)
    (hX8 : X % 8 = 0) (hX : 0x7b78 ≤ X) (hX' : X ≤ 0x84b0)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) (h30 : s.getReg .x30 = BitVec.ofNat 64 0x7b70) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if 0x7b70 < X - 8 then pcOf 42783 else pcOf 42787) ∧
      t.getReg .x29 = BitVec.ofNat 64 (X - 8) ∧
      t.getMem (BitVec.ofNat 64 (X + 8)) = s.getMem (BitVec.ofNat 64 (X - 8)) ∧
      RegsExcept s t [.x13, .x29] ∧ Frame s t (fun A => A = X + 8) := by
  refine ⟨_, symRun_sound h2_proL (codeAt_proL hP) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_proL.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h29, h30, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h29, h30]
    rw [m64_add8 X (by omega), m64_sub8 X (by omega) (by omega)]
    omega
  · simp only [Result.toState_pc, h2_proL.res, E.eval, CmpOp.eval, BinOp.eval, h29, h30]
    t3n [h29, h30]
    rw [ofNat_m8 X (by omega) (by omega)]
    simp only [BitVec.ult, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 31600 < 18446744073709551616 by norm_num),
      Nat.mod_eq_of_lt (show X - 8 < 18446744073709551616 by omega)]
    by_cases hc : 31600 < X - 8 <;> simp [hc, pcOf]
  · simp only [Result.toState_getReg, h2_proL.res]; t3n [h29]
    rw [m64_sub8 X (by omega) (by omega), Nat.mod_eq_of_lt (show X - 8 < 18446744073709551616 by omega)]
  · simp only [Result.toState_getMem, h2_proL.res]
    t3n [h29]
    rw [ofNat_m8 X (by omega) (by omega)]
  · ex_regs h2_proL.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_proL.res]
    t3n [h29]
    rw [m64_add8 X (by omega), Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by simpa using hn)]

theorem proB_spec {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 42787)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 0x7b70) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42794 ∧
      t.getMem (BitVec.ofNat 64 0x7b70) = s.getReg .x6 ∧ t.getMem (BitVec.ofNat 64 0x7b78) = s.getReg .x7 ∧
      t.getReg .x6 = 0 ∧ t.getReg .x7 = 0 ∧ t.getReg .x29 = 0 ∧ t.getReg .x30 = 0 ∧ t.getReg .x13 = 0 ∧
      RegsExcept s t [.x6, .x7, .x13, .x29, .x30] ∧ Frame s t (fun A => A = 0x7b70 ∨ A = 0x7b78) := by
  refine ⟨_, symRun_sound h2_proB (codeAt_proB hP) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [h2_proB.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h30, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    t3n [h30]
    all_goals first | omega | norm_num | skip
  · simp [Result.toState_pc, h2_proB.res, E.eval]
  · simp only [Result.toState_getMem, h2_proB.res]; t3n [h30]
  · simp only [Result.toState_getMem, h2_proB.res]; t3n [h30]
  · simp only [Result.toState_getReg, h2_proB.res]; t3n []
  · simp only [Result.toState_getReg, h2_proB.res]; t3n []
  · simp only [Result.toState_getReg, h2_proB.res]; t3n []
  · simp only [Result.toState_getReg, h2_proB.res]; t3n []
  · simp only [Result.toState_getReg, h2_proB.res]; t3n []
  · ex_regs h2_proB.res
  · intro A hA hn
    simp only [Result.toState_getMem, h2_proB.res]
    t3n [h30]
    rw [if_neg (by omega), if_neg (by omega)]

/-! ### The move loop -/

structure PInv (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 42783
  x29 : t.getReg .x29 = BitVec.ofNat 64 (0x84b0 - 8 * i)
  x30 : t.getReg .x30 = BitVec.ofNat 64 0x7b70
  x6 : t.getReg .x6 = s0.getMem (BitVec.ofNat 64 0x84b0)
  x7 : t.getReg .x7 = s0.getMem (BitVec.ofNat 64 0x84b8)
  hi : i ≤ 296
  moved : ∀ j < i, t.getMem (BitVec.ofNat 64 (0x84b8 - 8 * j)) = s0.getMem (BitVec.ofNat 64 (0x84a8 - 8 * j))
  regs : RegsExcept s0 t [.x6, .x7, .x13, .x29, .x30]
  frame : Frame s0 t (fun A => ∃ j < i, A = 0x84b8 - 8 * j)

theorem proLoop {im : Image} (hP : ProAt im) {s0 u : MachineState} (h0 : PInv s0 0 u) :
    ∀ i, i ≤ 295 → ∃ t, Steps im u (4 * i) (4 * i) t ∧ PInv s0 i t := by
  intro i
  induction i with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ i ih =>
    intro hi
    obtain ⟨t, st, ht⟩ := ih (by omega)
    obtain ⟨t', st', p', x29', m', r', f'⟩ := proL_spec hP t ht.pc (0x84b0 - 8 * i) (by omega) (by omega) (by omega)
      ht.x29 ht.x30
    rw [if_pos (by omega)] at p'
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), ⟨p', by rw [x29', show 33968 - 8 * i - 8 = 33968 - 8 * (i + 1) by omega],
      by rw [r'.get (by decide)]; exact ht.x30, by rw [r'.get (by decide)]; exact ht.x6,
      by rw [r'.get (by decide)]; exact ht.x7, by omega, fun j hj => ?_, (ht.regs.trans r').mono (by decide),
      fun A hA hn => ?_⟩⟩
    · by_cases hji : j < i
      · rw [f'.get (by omega) (by omega)]; exact ht.moved j hji
      · have hj : j = i := by omega
        subst hj
        rw [show 0x84b8 - 8 * j = 0x84b0 - 8 * j + 8 by omega, m',
          show 0x84b0 - 8 * j - 8 = 0x84a8 - 8 * j by omega,
          ht.frame.get (by omega) (by rintro ⟨j', hj', e⟩; omega)]
    · rw [f'.get hA (fun h => hn ⟨i, by omega, by omega⟩),
        ht.frame.get hA (fun ⟨j, hj, e⟩ => hn ⟨j, by omega, e⟩)]

/-- The whole prologue, from reset to word 1. -/
theorem prologue_spec {im : Image} (hP : ProAt im) (s0 : MachineState) (hpc : s0.pc = pcOf 0)
    (hz : ∀ r, r ∈ [Reg.x6, .x7, .x13, .x29, .x30] → s0.getReg r = 0) :
    ∃ u, Steps im s0 1199 1199 u ∧ u.pc = pcOf 1 ∧ (∀ r, u.getReg r = s0.getReg r) ∧
      u.getMem (BitVec.ofNat 64 0x7b70) = s0.getMem (BitVec.ofNat 64 0x84b0) ∧
      u.getMem (BitVec.ofNat 64 0x7b78) = s0.getMem (BitVec.ofNat 64 0x84b8) ∧
      (∀ j < 296, u.getMem (BitVec.ofNat 64 (0x84b8 - 8 * j)) = s0.getMem (BitVec.ofNat 64 (0x84a8 - 8 * j))) ∧
      Frame s0 u (fun A => A = 0x7b70 ∨ A = 0x7b78 ∨ ∃ j < 296, A = 0x84b8 - 8 * j) := by
  have s1 := w0_step hP s0 hpc
  set u1 := s0.setPC (pcOf 42777) with hu1
  obtain ⟨u2, s2, p2, x29, x30, x6, x7, r2, f2⟩ := proA_spec hP u1 rfl
  have h0 : PInv s0 0 u2 :=
    ⟨p2, by rw [x29], x30, by rw [x6]; rfl, by rw [x7]; rfl, by omega, fun j hj => absurd hj (by omega),
      fun r hr => by rw [r2.get (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))]; rfl, fun A hA hn => by rw [f2.get hA (fun h => h)]; rfl⟩
  obtain ⟨u3, s3, h3⟩ := proLoop hP h0 295 le_rfl
  obtain ⟨u4, s4, p4, x29', m4, r4, f4⟩ := proL_spec hP u3 h3.pc (0x84b0 - 8 * 295) (by decide) (by decide)
    (by decide) h3.x29 h3.x30
  rw [if_neg (by decide)] at p4
  have h4moved : ∀ j < 296, u4.getMem (BitVec.ofNat 64 (0x84b8 - 8 * j)) =
      s0.getMem (BitVec.ofNat 64 (0x84a8 - 8 * j)) := by
    intro j hj
    by_cases hji : j < 295
    · rw [f4.get (by omega) (by omega)]; exact h3.moved j hji
    · have hj : j = 295 := by omega
      subst hj
      rw [show 0x84b8 - 8 * 295 = 0x84b0 - 8 * 295 + 8 by decide, m4,
        show 0x84b0 - 8 * 295 - 8 = 0x84a8 - 8 * 295 by decide,
        h3.frame.get (by decide) (by rintro ⟨j', hj', e⟩; omega)]
  obtain ⟨u5, s5, p5, m70, m78, x6', x7', x29'', x30'', x13'', r5, f5⟩ := proB_spec hP u4 p4
    (by rw [r4.get (by decide)]; exact h3.x30)
  have s6 := proJ_step hP u5 p5
  refine ⟨u5.setPC (pcOf 1), (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))).of_eq (by norm_num)
    (by norm_num), rfl, fun r => ?_,
    ?_, ?_, fun j hj => ?_, fun A hA hn => ?_⟩
  · show u5.getReg r = s0.getReg r
    by_cases hr : r ∈ [Reg.x6, .x7, .x13, .x29, .x30]
    · rw [hz r hr]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> assumption
    · rw [r5.get hr, r4.get (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto)),
        h3.regs.get hr]
  · show u5.getMem _ = _
    rw [m70, r4.get (by decide), h3.x6]
  · show u5.getMem _ = _
    rw [m78, r4.get (by decide), h3.x7]
  · show u5.getMem _ = _
    rw [f5.get (by omega) (by omega)]; exact h4moved j hj
  · show u5.getMem _ = _
    rw [f5.get hA (fun h => hn (h.elim Or.inl (fun h => Or.inr (Or.inl h)))),
      f4.get hA (fun h => hn (Or.inr (Or.inr ⟨295, by omega, by omega⟩))),
      h3.frame.get hA (fun ⟨j, hj, e⟩ => hn (Or.inr (Or.inr ⟨j, by omega, e⟩)))]
    try rfl


/-! ### The un-shifted memory is the old expander's initial memory for `sigFull b` -/

def sigFull (b : Bytes 5310) : Bytes 5312 := ClaudeWCT.W9.T3M.sigB (ClaudeWCT.W9.T3M.sigDecC b)
theorem sigDec_sigFull (b : Bytes 5310) : ClaudeWCT.W9.T3M.sigDec (sigFull b) = ClaudeWCT.W9.T3M.sigDecC b :=
  ClaudeWCT.W9.T3M.sigDec_sigB _
def cw (j : Nat) : Nat := if j < 366 then j else if j < 368 then j + 296 else j - 2

theorem extract_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64 * i) 64 = x.extractLsb' (a + 64 * i) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ (64 * i) * 2 ^ (128 - 64 * i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)), Nat.div_div_eq_div_mul,
    ← pow_add]

theorem sigFull_word (b : Bytes 5310) (j : Nat) (hj : j < 664) :
    (sigFull b).extractLsb' (64 * j) 64 = b.extractLsb' (64 * cw j) 64 := by
  have hk : j / 2 < 332 := by omega
  have e1 : (sigFull b).extractLsb' (64 * j) 64 =
      ((sigFull b).extractLsb' (128 * (j / 2)) 128).extractLsb' (64 * (j % 2)) 64 := by
    rw [extract_word _ _ _ (Nat.mod_lt _ (by decide))]; congr 1; omega
  have e2 : (sigFull b).extractLsb' (128 * (j / 2)) 128 = ClaudeWCT.W9.T3M.digC b (j / 2) := by
    show ClaudeWCT.W9.T3M.sigDig (sigFull b) (j / 2) = _
    rw [sigFull, ClaudeWCT.W9.T3M.sigDig_sigB, ClaudeWCT.W9.T3M.sigDigests_sigDecC b _ hk]
  rw [e1, e2]
  unfold ClaudeWCT.W9.T3M.digC ClaudeWCT.W9.T3M.cDig cw
  by_cases h1 : j / 2 < 183
  · rw [if_pos h1, extract_word _ _ _ (Nat.mod_lt _ (by decide)), if_pos (by omega)]; congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : j / 2 = 183
    · rw [if_pos h2, extract_word _ _ _ (Nat.mod_lt _ (by decide)), if_neg (by omega), if_pos (by omega)]
      congr 1; omega
    · rw [if_neg h2, extract_word _ _ _ (Nat.mod_lt _ (by decide)), if_neg (by omega), if_neg (by omega)]
      congr 1; omega

/-- The last, partial word of a byte string (the high bytes read as zero). -/
theorem bytesToWordLE_bytes_tail {n : Nat} (x : Bytes n) (j : Nat) (hj : 8 * j < n) :
    bytesToWordLE (((bytes x).drop (8 * j)).take 8) = x.extractLsb' (64 * j) 64 := by
  apply word_ext_bytes_e
  intro i hi
  rw [extractByte_bytesToWordLE_e _ _ hi]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat_e]
  by_cases hin : 8 * j + i < n
  · simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, List.getElem?_range hin, if_pos hi, Option.map_some,
      Option.getD_some, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (8 * j + i) = 64 * j + 8 * i by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
    generalize x.toNat / 2 ^ (64 * j) = y
    interval_cases i <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, pow_zero, Nat.div_one] <;> omega
  · have hnone : (List.range n)[8 * j + i]? = none := List.getElem?_eq_none (by simp; omega)
    simp only [bytes, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop,
      List.getElem?_map, hnone, if_pos hi, Option.map_none, Option.getD_none,
      BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    have hx := x.isLt
    have hlt : x.toNat < 2 ^ (64 * j + 8 * i) := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [show (2 : Nat) ^ (64 * j + 8 * i) = 2 ^ (64 * j) * 2 ^ (8 * i) by rw [← pow_add]] at hlt
    have h0 : x.toNat / 2 ^ (64 * j) / 2 ^ (8 * i) = 0 := by
      rw [Nat.div_div_eq_div_mul]; exact Nat.div_eq_of_lt hlt
    change 0 = x.toNat / 2 ^ (64 * j) % 2 ^ 64 / 2 ^ (8 * i) % 256
    rw [show x.toNat / 2 ^ (64 * j) % 2 ^ 64 / 2 ^ (8 * i) % 256 = 0 by
      rw [show (2 : Nat) ^ 64 = 2 ^ (8 * i) * 2 ^ (64 - 8 * i) by rw [← pow_add]; congr 1; omega,
        Nat.mod_mul_right_div_self, h0]; simp]

section mem
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (b : Bytes 5310)
include hd
theorem w9initC_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5312 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes b).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x65E0 ≤ A ∧ A < 0x6600 ∧ (A - 0x65E0) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x65E0)).take 8)
      else if Compact2.LPLAN ≤ A ∧ A < Compact2.LPLAN + 27648 ∧ (A - Compact2.LPLAN) % 8 = 0 then
        bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x65E0 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ Compact2.LPLAN A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9initC_word (j : Nat) (hj : j < 664) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64 := by
  rw [w9initC_getMem hd m pk b _ (by omega), if_pos (by omega), show 0x7000 + 8 * j - 0x7000 = 8 * j by omega,
    bytesToWordLE_bytes_tail b j (by omega)]
omit hd in
theorem w9initC_pc : (w9init im m pk b).pc = pcOf 0 := by
  unfold w9init
  rw [MachineState.pc_setReg, MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords,
    MachineState.pc_writeBytesAsWords, MachineState.pc_writeBytesAsWords]
  rfl
theorem w9init_regs0 (r : Reg) (hr : r ≠ .x2) : (w9init im m pk b).getReg r = 0 := by
  unfold w9init
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  simp only [MachineState.getReg_writeBytesAsWords]
  cases r <;> rfl
/-- After the prologue the memory is the old initial memory for the full-layout bytes. -/
theorem prologue_mem (u : MachineState)
    (h70 : u.getMem (BitVec.ofNat 64 0x7b70) = (w9init im m pk b).getMem (BitVec.ofNat 64 0x84b0))
    (h78 : u.getMem (BitVec.ofNat 64 0x7b78) = (w9init im m pk b).getMem (BitVec.ofNat 64 0x84b8))
    (hmv : ∀ j < 296, u.getMem (BitVec.ofNat 64 (0x84b8 - 8 * j)) =
      (w9init im m pk b).getMem (BitVec.ofNat 64 (0x84a8 - 8 * j)))
    (hf : Frame (w9init im m pk b) u (fun A => A = 0x7b70 ∨ A = 0x7b78 ∨ ∃ j < 296, A = 0x84b8 - 8 * j)) :
    ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) = (w9init im m pk (sigFull b)).getMem (BitVec.ofNat 64 A) := by
  intro A hA
  rw [w9init_getMem hd m pk (sigFull b) A hA]
  by_cases hs : 0x7000 ≤ A ∧ A < 0x7000 + 5312 ∧ (A - 0x7000) % 8 = 0
  · rw [if_pos hs]
    obtain ⟨j, rfl⟩ : ∃ j, A = 0x7000 + 8 * j := ⟨(A - 0x7000) / 8, by omega⟩
    have hj : j < 664 := by omega
    rw [show 0x7000 + 8 * j - 0x7000 = 8 * j by omega, bytesToWordLE_bytes_e (sigFull b) j (by omega),
      sigFull_word b j hj]
    unfold cw
    by_cases h1 : j < 366
    · rw [if_pos h1, hf.get hA (by rintro (h | h | ⟨j', hj', e⟩) <;> omega), w9initC_word hd m pk b j hj]
    · rw [if_neg h1]
      by_cases h2 : j < 368
      · rw [if_pos h2]
        by_cases h3 : j = 366
        · subst h3
          rw [h70, show (0x84b0 : Nat) = 0x7000 + 8 * 662 from rfl, w9initC_word hd m pk b 662 (by decide)]
        · have h4 : j = 367 := by omega
          subst h4
          rw [h78, show (0x84b8 : Nat) = 0x7000 + 8 * 663 from rfl, w9initC_word hd m pk b 663 (by decide)]
      · rw [if_neg h2]
        have := hmv (663 - j) (by omega)
        rw [show 0x84b8 - 8 * (663 - j) = 0x7000 + 8 * j by omega,
          show 0x84a8 - 8 * (663 - j) = 0x7000 + 8 * (j - 2) by omega, w9initC_word hd m pk b (j - 2) (by omega)]
          at this
        exact this
  · rw [if_neg hs, hf.get hA (by rintro (h | h | ⟨j', hj', e⟩) <;> omega), w9initC_getMem hd m pk b A hA,
      if_neg hs]
end mem

/-- [h2 lane] the record's front from word 1 (word 0 is now the jump to the prologue): 29 steps to the zero block. -/
theorem front_spec' {im : Image} (hP : ProAt im) (s : MachineState)
    (hpc : s.pc = pcOf 1) (hx5 : s.getReg .x5 = 0) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 42719 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x65E0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x65E8) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x65F0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x65F8) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound h2_front hP.2.2 s hpc
    (by simp [h2_front.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_front.res, E.eval]
  · simp [h2_front.res, rv_simp, hx5]
  iterate 8
    · simp only [Result.toState_getMem, h2_front.res, DIG]
      t3n []
  · ex_regs h2_front.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, h2_front.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
/-- [h2 lane] the record's `front_pre30` from the prologue's exit state `u` (pc at word 1, memory = the full-layout
initial memory): front (29) then the zero block (7). -/
theorem front_pre30' {im : Image} (hF : FrontAt im) (hP : ProAt im) (hd : ExpandDataOK im) (m : Message)
    (pk : PublicKey) (σ : Bytes 5312) (u : MachineState) (hupc : u.pc = pcOf 1) (hu5 : u.getReg .x5 = 0)
    (humem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) = (w9init im m pk σ).getMem (BitVec.ofNat 64 A)) :
    ∃ t, Steps im u 36 36 t ∧ Pre30 m (sigDec σ) t ∧
      (∀ A, A < 2 ^ 64 → (A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) → t.getMem (BitVec.ofNat 64 A) = 0) ∧
      t.getMem (BitVec.ofNat 64 0x800) = (sigDec σ).rho.extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 0x808) = (sigDec σ).rho.extractLsb' 64 64 ∧
      Frame (w9init im m pk σ) t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
        A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) := by
  set s := w9init im m pk σ
  obtain ⟨t0, st0, p0, x5_0, w800, w808, d0, d8, d32, d40, d48, d56, r0, f0'⟩ := front_spec' hP u hupc hu5
  have f0 : Frame s t0 (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) :=
    fun A hA hn => (f0' A hA hn).trans (humem A hA)
  rw [humem 0x7000 (by decide)] at w800 d0
  rw [humem 0x7008 (by decide)] at w808 d8
  rw [humem 0x65E0 (by decide)] at d32
  rw [humem 0x65E8 (by decide)] at d40
  rw [humem 0x65F0 (by decide)] at d48
  rw [humem 0x65F8 (by decide)] at d56
  obtain ⟨t, st1, p, x19, z, r1, f1⟩ := zero_spec hF.2 t0 p0
  have f : Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
      A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) :=
    (f0.trans f1).mono (fun A _ h => by
      rcases h with h | h
      · rcases h with h | h | h | h | h | h | h | h <;> simp [h]
      · rcases h with h | h | h | h <;> simp [h])
  have g : ∀ A, A < 2 ^ 64 → ¬ (A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8) →
      t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) := fun A hA h => f1 A hA h
  have hrho : DigAt s 0x7000 (sigDec σ).rho := w9init_sig hd m pk σ 0 (by decide)
  have hsd : ∀ k, k < 332 → DigAt t (0x7000 + 16 * k) ((sigDigests (sigDec σ)).getD k 0) := by
    intro k hk
    have := w9init_sig hd m pk σ k hk
    rw [sigDigests_sigDec σ k hk]
    exact ⟨(f _ (by omega) (by simp only [DIG]; omega)).trans this.1,
      (f _ (by omega) (by simp only [DIG]; omega)).trans this.2⟩
  refine ⟨t, st0.trans st1, ⟨p, by rw [r1.get (by decide), x5_0], x19,
      ⟨(g _ (by decide) (by simp only [DIG]; omega)).trans (d0.trans hrho.1),
        (g _ (by decide) (by simp only [DIG]; omega)).trans (d8.trans hrho.2)⟩, fun k hk => ?_, hsd,
      fun A h1 h2 => ?_, fun A h1 h2 => ?_,
      hdrBank_frame (w9init_bank hd m pk σ) f (fun A h1 h2 h => by simp only [DIG] at h; unfold HB0 at h1; omega),
      fun k hk => (f _ (by unfold ECOST; omega) (by simp only [DIG]; unfold ECOST; omega)).trans
        (w9init_cost hd m pk σ k hk),
      fun k hk => (f _ (by unfold PLAN; omega) (by simp only [DIG]; unfold PLAN; omega)).trans
        (w9init_plan hd m pk σ k hk)⟩, z,
    (g _ (by decide) (by omega)).trans (w800.trans hrho.1), (g _ (by decide) (by omega)).trans (w808.trans hrho.2), f⟩
  · have hm : ∀ j, j < 4 → t.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * j)) = m.extractLsb' (64 * j) 64 := by
      intro j hj
      rw [g _ (by simp only [DIG]; omega) (by simp only [DIG]; omega)]
      interval_cases j
      · rw [show DIG + 32 + 8 * 0 = DIG + 32 by rfl, d32]; simpa using w9init_msg hd m pk σ 0 (by decide)
      · rw [show DIG + 32 + 8 * 1 = DIG + 40 by rfl, d40]; simpa using w9init_msg hd m pk σ 1 (by decide)
      · rw [show DIG + 32 + 8 * 2 = DIG + 48 by rfl, d48]; simpa using w9init_msg hd m pk σ 2 (by decide)
      · rw [show DIG + 32 + 8 * 3 = DIG + 56 by rfl, d56]; simpa using w9init_msg hd m pk σ 3 (by decide)
    exact hm k hk
  · rw [f A (by omega) (by simp only [DIG]; omega)]
    exact w9init_zero hd m pk σ A (by unfold Compact2.LPLAN; omega) ⟨by omega, by omega, by omega⟩
  · rw [f A (by omega) (by simp only [DIG]; omega)]
    exact w9init_zero hd m pk σ A (by unfold Compact2.LPLAN; omega) ⟨by omega, by omega, by omega⟩

end ClaudeWCT.W9.Machine.Expand
end

/-! Checked compact-layout prologue prototype; the image entrypoint is not yet redirected. -/
namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def prologueBase : Nat := 44096
def policyAddress : Nat := 417792
def prologueWords : List (BitVec 32) := [0x8eb7,0x470e8e93,0xeb303,0x8eb383,0x303de13,0x66f37,0xf0f13,0x1cf3023,0x1039393,0x103d393,0x17b7,0x6c878793,0x14fe7863,0x8eb7,0x468e8e93,0x8f37,0x4b8f0f13,0x87b7,0xb3078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x8f37,0xb70f0f13,0x6f3023,0x7f3423,0x8eb7,0xb28e8e93,0x8f37,0xb68f0f13,0x77b7,0x58078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x5b0f0f13,0xf3023,0xf3423,0x7eb7,0x578e8e93,0x7f37,0x5a8f0f13,0x77b7,0x3f078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x410f0f13,0xf3023,0xf3423,0x7eb7,0x3e8e8e93,0x7f37,0x408f0f13,0x77b7,0x26078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0x270f0f13,0xf3023,0xf3423,0x7eb7,0x258e8e93,0x7f37,0x268f0f13,0x77b7,0xd078793,0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3,0x7f37,0xd0f0f13,0xf3023,0xf3423,0x313,0x393,0x713,0x793,0xe13,0xe93,0xf13,0xd89d406f,0xb08d506f]
def tailWords : List (BitVec 32) := [0x8eb7,0x470e8e93,0xeb303,0x8eb383,0x303de13,0x66f37,0xf0f13,0x1cf3023,0x1039393,0x103d393]

sym_block tailRun := symRun { noAlias := true } tailWords (pcOf prologueBase) 50

theorem tail_spec {im : Image} (hc : CodeAt im (pcOf prologueBase) tailWords)
    (s : MachineState) (hpc : s.pc = pcOf prologueBase) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf (prologueBase + 10) ∧
      t.getReg .x6 = s.getMem 0x8470 ∧
      t.getReg .x7 = (s.getMem 0x8478 <<< 16) >>> 16 ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = s.getMem 0x8478 >>> 48 ∧
      Frame s t (fun A => A = policyAddress) := by
  refine ⟨_, symRun_sound tailRun hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tailRun.res, rv_simp, accessValid_iff, MEMORY_BYTES, prologueBase, policyAddress]
  · simp [Result.toState_pc, tailRun.res, E.eval, prologueBase, pcOf]
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getMem, tailRun.res]; t3n [policyAddress]
  · intro A hA hne
    simp only [Result.toState_getMem, tailRun.res]
    t3n [policyAddress]
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by simpa [policyAddress] using hne)]

#print axioms tail_spec
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def guardWords : List (BitVec 32) := [0x17b7,0x6c878793,0x14fe7863]
sym_block guardRun := symRun { noAlias := true } guardWords (pcOf 44106) 20

theorem guard_spec {im : Image} (hc : CodeAt im (pcOf 44106) guardWords)
    (s : MachineState) (hpc : s.pc = pcOf 44106)
    (H : Nat) (hH : H < 65536) (hr : s.getReg .x28 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if H < 5832 then pcOf 44109 else pcOf 44192) ∧
      RegsExcept s t [.x15] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound guardRun hc s hpc ?_, ?_, ?_, ?_⟩
  · simp [guardRun.res, rv_simp]
  · simp only [Result.toState_pc, guardRun.res, rv_simp, hr]
    by_cases h : H < 5832
    · simp [h, BitVec.ult]
      omega
    · simp [h, BitVec.ult]
      omega
  · intro r h
    cases r <;> simp_all [rv_simp, guardRun.res] <;> rfl
  · intro A hA h
    rfl

#print axioms guard_spec

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
def copyWords : List (BitVec 32) := [0xeb703,0xef3023,0xff8e8e93,0xff8f0f13,0xfefef8e3]
sym_block copyRun := symRun { noAlias := true } copyWords (pcOf (prologueBase + 16)) 50

def copyResult (p : Word) : Result :=
  ⟨copyRun.res.st,
    .ite .geu (.bin .add (.reg .x29) (.c 18446744073709551608)) (.reg .x15)
      (.c (((((p + 4) + 4) + 4) + 4) + 18446744073709551600))
      (.c (((((p + 4) + 4) + 4) + 4) + 4)), .branch, 5, 5⟩

theorem copy_run (p : Word) :
    symRun { noAlias := true } copyWords p 50 = some (copyResult p) := by krfl

#print axioms copy_run
theorem ofNat_sub_eight (n : Nat) :
    (BitVec.ofNat 64 (n + 8) + 18446744073709551608 : Word) = BitVec.ofNat 64 n := by
  rw [show (18446744073709551608 : Word) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
    ofNat_add_ofNat,
    show n + 8 + (2 ^ 64 - 8) = n + 2 ^ 64 by omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.add_mod_right]


theorem branch_not_lt {α : Type} (a b : α) (X Z : Nat) :
    (if (!decide (X < Z)) = true then a else b) = (if Z ≤ X then a else b) := by
  by_cases h : X < Z
  · simp only [h, decide_true, Bool.not_true, Bool.false_eq_true, if_false,
      show ¬Z ≤ X by omega]
  · simp only [h, decide_false, Bool.not_false, if_true, show Z ≤ X by omega]


theorem copy_regs (p : Word) (s : MachineState) :
    RegsExcept s ((copyResult p).toState s) [.x14,.x29,.x30] := by
  intro r hr
  rw [Result.toState_getReg]
  change (copyRun.res.st.regs.get r).eval s = s.getReg r
  clear p
  cases r
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hr (by decide)).elim
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact (hr (by decide)).elim
  · exact (hr (by decide)).elim
  · rfl

#print axioms copy_regs

theorem copy_mem_frame (p : Word) (s : MachineState) (a : Word)
    (ha : a ≠ s.getReg .x30) :
    ((copyResult p).toState s).getMem a = s.getMem a := by
  simp only [Result.toState_getMem, copyResult, copyRun.res, memEval, Addr.eval, E.eval,
    BitVec.add_zero, if_neg ha]

#print axioms copy_mem_frame

theorem copy_frame (p : Word) (s : MachineState) (Y : Nat) (hY : Y < 2 ^ 64)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 Y) :
    Frame s ((copyResult p).toState s) (fun A => A = Y) := by
  intro A hA hne
  apply copy_mem_frame p s (BitVec.ofNat 64 A)
  rw [h30]
  intro he
  exact hne ((ofNat_inj hA hY).mp he)

#print axioms copy_frame

theorem copy_step {im : Image} (p : Word) (hc : CodeAt im p copyWords)
    (s : MachineState) (hpc : s.pc = p) (X Y Z : Nat)
    (hX8 : X % 8 = 0) (hY8 : Y % 8 = 0)
    (hX : 8 ≤ X) (hY : 8 ≤ Y) (hX' : X ≤ 0x8500) (hY' : Y ≤ 0x8500) (hZ : Z < 2 ^ 64)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 Y)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 Z) :
    ∃ t, Steps im s 5 5 t ∧
      t.pc = (if Z ≤ X - 8 then p else p + 20) ∧
      t.getReg .x29 = BitVec.ofNat 64 (X - 8) ∧
      t.getReg .x30 = BitVec.ofNat 64 (Y - 8) ∧
      t.getMem (BitVec.ofNat 64 Y) = s.getMem (BitVec.ofNat 64 X) ∧
      RegsExcept s t [.x14, .x29, .x30] ∧ Frame s t (fun A => A = Y) := by
  refine ⟨_, symRun_sound (copy_run p) hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [copyResult, copyRun.res, rv_simp, h29, h30, accessValid_iff, MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc, copyResult, E.eval, BinOp.eval, CmpOp.eval, h29, h15]
    have hxsub : (BitVec.ofNat 64 X + 18446744073709551608 : Word) = BitVec.ofNat 64 (X - 8) := by
      simpa only [Nat.sub_add_cancel hX] using ofNat_sub_eight (X - 8)
    rw [hxsub]
    simp only [BitVec.ult, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show X - 8 < 2 ^ 64 by omega), Nat.mod_eq_of_lt hZ]
    have hb : (((p + 4) + 4) + 4) + 4 + 18446744073709551600 = p := by
      simp only [BitVec.add_assoc]
      change p + 0 = p
      exact BitVec.add_zero p
    have he : (((p + 4) + 4) + 4) + 4 + 4 = p + 20 := by
      simp only [BitVec.add_assoc]
      rfl
    rw [hb, he]
    exact branch_not_lt p (p + 20) (X - 8) Z
  · rw [Result.toState_getReg]
    change s.getReg .x29 + 18446744073709551608 = _
    rw [h29]
    simpa only [Nat.sub_add_cancel hX] using ofNat_sub_eight (X - 8)
  · rw [Result.toState_getReg]
    change s.getReg .x30 + 18446744073709551608 = _
    rw [h30]
    simpa only [Nat.sub_add_cancel hY] using ofNat_sub_eight (Y - 8)
  · simp only [Result.toState_getMem, copyResult, copyRun.res]
    t3n [h29, h30]
    simp only [Nat.add_zero, if_true]
  · exact copy_regs p s
  · exact copy_frame p s Y (by omega) h30

#print axioms copy_step

theorem copy_loop {im : Image} (p : Word) (hc : CodeAt im p copyWords)
    (S D : Nat) (hS8 : S % 8 = 0) (hD8 : D % 8 = 0) (hS : 8 ≤ S) (hSD : S < D) :
    ∀ n (s : MachineState), D + 8 * n ≤ 0x8500 → s.pc = p →
      s.getReg .x29 = BitVec.ofNat 64 (S + 8 * n) →
      s.getReg .x30 = BitVec.ofNat 64 (D + 8 * n) →
      s.getReg .x15 = BitVec.ofNat 64 S →
      ∃ t, Steps im s (5 * (n + 1)) (5 * (n + 1)) t ∧ t.pc = p + 20 ∧
        t.getReg .x29 = BitVec.ofNat 64 (S - 8) ∧
        t.getReg .x30 = BitVec.ofNat 64 (D - 8) ∧
        (∀ i, i ≤ n → t.getMem (BitVec.ofNat 64 (D + 8 * i)) =
          s.getMem (BitVec.ofNat 64 (S + 8 * i))) ∧
        RegsExcept s t [.x14, .x29, .x30] ∧
        Frame s t (fun A => D ≤ A ∧ A < D + 8 * (n + 1)) := by
  intro n
  induction n with
  | zero =>
      intro s hbound hpc h29 h30 h15
      simp only [Nat.mul_zero, Nat.add_zero] at h29 h30 hbound
      obtain ⟨t, st, pt, r29, r30, mt, rt, ft⟩ := copy_step p hc s hpc S D S
        hS8 hD8 hS (by omega) (by omega) hbound (by omega) h29 h30 h15
      refine ⟨t, by simpa using st, ?_, r29, r30, ?_, rt, ?_⟩
      · simpa only [show ¬S ≤ S - 8 by omega, if_false] using pt
      · intro i hi
        have hi0 : i = 0 := by omega
        simpa only [hi0, Nat.mul_zero, Nat.add_zero] using mt
      · exact ft.mono (by intro A _ hA; omega)
  | succ n ih =>
      intro s hbound hpc h29 h30 h15
      obtain ⟨u, su, pu, u29, u30, mu, ru, fu⟩ := copy_step p hc s hpc
        (S + 8 * (n + 1)) (D + 8 * (n + 1)) S
        (by omega) (by omega) (by omega) (by omega) (by omega) hbound (by omega) h29 h30 h15
      have hu29 : u.getReg .x29 = BitVec.ofNat 64 (S + 8 * n) := by
        rw [u29, show S + 8 * (n + 1) - 8 = S + 8 * n by omega]
      have hu30 : u.getReg .x30 = BitVec.ofNat 64 (D + 8 * n) := by
        rw [u30, show D + 8 * (n + 1) - 8 = D + 8 * n by omega]
      have hpu : u.pc = p := by
        simpa only [show S ≤ S + 8 * (n + 1) - 8 by omega, if_true] using pu
      obtain ⟨t, ut, pt, r29, r30, mt, rt, ft⟩ := ih u (by omega) hpu hu29 hu30
        ((ru .x15 (by simp)).trans h15)
      refine ⟨t, ?_, pt, r29, r30, ?_, ?_, ?_⟩
      · convert su.trans ut using 1 <;> omega
      · intro i hi
        by_cases hin : i ≤ n
        · rw [mt i hin]
          exact fu _ (by omega) (by omega)
        · have hi' : i = n + 1 := by omega
          subst i
          rw [ft _ (by omega) (by omega)]
          exact mu
      · intro r hr
        exact (rt r hr).trans (ru r hr)
      · exact (fu.trans ft).mono (by intro A _ hA; rcases hA with hA | hA <;> omega)

#print axioms copy_loop


end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def mainHighSetupWords : List (BitVec 32) := [0x8eb7,0x468e8e93,0x8f37,0x4b8f0f13,0x87b7,0xb3078793]
sym_block mainHighSetup := symRun { noAlias := true } mainHighSetupWords (pcOf 44109) 30

theorem mainHigh_setup {im : Image} (hc : CodeAt im (pcOf 44109) mainHighSetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44109) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44115 ∧
      t.getReg .x29 = BitVec.ofNat 64 33896 ∧
      t.getReg .x30 = BitVec.ofNat 64 33976 ∧
      t.getReg .x15 = BitVec.ofNat 64 31536 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound mainHighSetup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [mainHighSetup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem mainHigh_move {im : Image} (hs : CodeAt im (pcOf 44109) mainHighSetupWords)
    (hc : CodeAt im (pcOf 44115) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44109) :
    ∃ t, Steps im s 1486 1486 t ∧ t.pc = pcOf 44120 ∧
      (∀ i, i ≤ 295 → t.getMem (BitVec.ofNat 64 (31616 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (31536 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 31616 ≤ A ∧ A < 33984) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := mainHigh_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44115) hc 31536 31616
    (by decide) (by decide) (by decide) (by decide) 295 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms mainHigh_move


def middleSetupWords : List (BitVec 32) := [0x8eb7,0xb28e8e93,0x8f37,0xb68f0f13,0x77b7,0x58078793]
sym_block middleSetup := symRun { noAlias := true } middleSetupWords (pcOf 44124) 30

theorem middle_setup {im : Image} (hc : CodeAt im (pcOf 44124) middleSetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44124) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44130 ∧
      t.getReg .x29 = BitVec.ofNat 64 31528 ∧
      t.getReg .x30 = BitVec.ofNat 64 31592 ∧
      t.getReg .x15 = BitVec.ofNat 64 30080 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound middleSetup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [middleSetup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem middle_move {im : Image} (hs : CodeAt im (pcOf 44124) middleSetupWords)
    (hc : CodeAt im (pcOf 44130) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44124) :
    ∃ t, Steps im s 916 916 t ∧ t.pc = pcOf 44135 ∧
      (∀ i, i ≤ 181 → t.getMem (BitVec.ofNat 64 (30144 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (30080 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 30144 ≤ A ∧ A < 31600) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := middle_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44130) hc 30080 30144
    (by decide) (by decide) (by decide) (by decide) 181 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms middle_move


def pair3SetupWords : List (BitVec 32) := [0x7eb7,0x578e8e93,0x7f37,0x5a8f0f13,0x77b7,0x3f078793]
sym_block pair3Setup := symRun { noAlias := true } pair3SetupWords (pcOf 44139) 30

theorem pair3_setup {im : Image} (hc : CodeAt im (pcOf 44139) pair3SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44139) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44145 ∧
      t.getReg .x29 = BitVec.ofNat 64 30072 ∧
      t.getReg .x30 = BitVec.ofNat 64 30120 ∧
      t.getReg .x15 = BitVec.ofNat 64 29680 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair3Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair3Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair3_move {im : Image} (hs : CodeAt im (pcOf 44139) pair3SetupWords)
    (hc : CodeAt im (pcOf 44145) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44139) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44150 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29728 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (29680 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 29728 ≤ A ∧ A < 30128) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair3_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44145) hc 29680 29728
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair3_move


def pair2SetupWords : List (BitVec 32) := [0x7eb7,0x3e8e8e93,0x7f37,0x408f0f13,0x77b7,0x26078793]
sym_block pair2Setup := symRun { noAlias := true } pair2SetupWords (pcOf 44154) 30

theorem pair2_setup {im : Image} (hc : CodeAt im (pcOf 44154) pair2SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44154) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44160 ∧
      t.getReg .x29 = BitVec.ofNat 64 29672 ∧
      t.getReg .x30 = BitVec.ofNat 64 29704 ∧
      t.getReg .x15 = BitVec.ofNat 64 29280 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair2Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair2Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair2_move {im : Image} (hs : CodeAt im (pcOf 44154) pair2SetupWords)
    (hc : CodeAt im (pcOf 44160) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44154) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44165 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29312 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (29280 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 29312 ≤ A ∧ A < 29712) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair2_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44160) hc 29280 29312
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair2_move


def pair1SetupWords : List (BitVec 32) := [0x7eb7,0x258e8e93,0x7f37,0x268f0f13,0x77b7,0xd078793]
sym_block pair1Setup := symRun { noAlias := true } pair1SetupWords (pcOf 44169) 30

theorem pair1_setup {im : Image} (hc : CodeAt im (pcOf 44169) pair1SetupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44169) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 44175 ∧
      t.getReg .x29 = BitVec.ofNat 64 29272 ∧
      t.getReg .x30 = BitVec.ofNat 64 29288 ∧
      t.getReg .x15 = BitVec.ofNat 64 28880 ∧
      RegsExcept s t [.x15,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound pair1Setup hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pair1Setup.res, rv_simp]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA h
    rfl

theorem pair1_move {im : Image} (hs : CodeAt im (pcOf 44169) pair1SetupWords)
    (hc : CodeAt im (pcOf 44175) copyWords)
    (s : MachineState) (hpc : s.pc = pcOf 44169) :
    ∃ t, Steps im s 256 256 t ∧ t.pc = pcOf 44180 ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (28896 + 8 * i)) =
        s.getMem (BitVec.ofNat 64 (28880 + 8 * i))) ∧
      RegsExcept s t [.x14,.x15,.x29,.x30] ∧
      Frame s t (fun A => 28896 ≤ A ∧ A < 29296) := by
  obtain ⟨u,su,pu,u29,u30,u15,ru,fu⟩ := pair1_setup hs s hpc
  obtain ⟨t,ut,pt,r29,r30,mt,rt,ft⟩ := copy_loop (pcOf 44175) hc 28880 28896
    (by decide) (by decide) (by decide) (by decide) 49 u (by decide) pu u29 u30 u15
  refine ⟨t, su.trans ut, ?_, ?_, ?_, ?_⟩
  · exact pt
  · intro i hi
    rw [mt i hi]
    exact fu _ (by omega) (by simp)
  · exact (ru.trans rt).mono (by decide)
  · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h; exact h.elim; exact h)

#print axioms pair1_move

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def restoreTailWords : List (BitVec 32) := [0x8f37,0xb70f0f13,0x6f3023,0x7f3423]
sym_block restoreTailRun := symRun { noAlias := true } restoreTailWords (pcOf 44120) 20

theorem restoreTail_spec {im : Image} (hc : CodeAt im (pcOf 44120) restoreTailWords)
    (s : MachineState) (hpc : s.pc = pcOf 44120) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44124 ∧
      t.getMem 31600 = s.getReg .x6 ∧ t.getMem 31608 = s.getReg .x7 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 31600 ∨ A = 31608) := by
  refine ⟨_, symRun_sound restoreTailRun hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [restoreTailRun.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [restoreTailRun.res, rv_simp]
  · simp [restoreTailRun.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, restoreTailRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms restoreTail_spec

def zero91Words : List (BitVec 32) := [0x7f37,0x5b0f0f13,0xf3023,0xf3423]
sym_block zero91Run := symRun { noAlias := true } zero91Words (pcOf 44135) 20

theorem zero91_spec {im : Image} (hc : CodeAt im (pcOf 44135) zero91Words)
    (s : MachineState) (hpc : s.pc = pcOf 44135) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44139 ∧
      t.getMem 30128 = 0 ∧ t.getMem 30136 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 30128 ∨ A = 30136) := by
  refine ⟨_, symRun_sound zero91Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero91Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero91Run.res, rv_simp]
  · simp [zero91Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero91Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero91_spec

def zero65Words : List (BitVec 32) := [0x7f37,0x410f0f13,0xf3023,0xf3423]
sym_block zero65Run := symRun { noAlias := true } zero65Words (pcOf 44150) 20

theorem zero65_spec {im : Image} (hc : CodeAt im (pcOf 44150) zero65Words)
    (s : MachineState) (hpc : s.pc = pcOf 44150) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44154 ∧
      t.getMem 29712 = 0 ∧ t.getMem 29720 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 29712 ∨ A = 29720) := by
  refine ⟨_, symRun_sound zero65Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero65Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero65Run.res, rv_simp]
  · simp [zero65Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero65Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero65_spec

def zero39Words : List (BitVec 32) := [0x7f37,0x270f0f13,0xf3023,0xf3423]
sym_block zero39Run := symRun { noAlias := true } zero39Words (pcOf 44165) 20

theorem zero39_spec {im : Image} (hc : CodeAt im (pcOf 44165) zero39Words)
    (s : MachineState) (hpc : s.pc = pcOf 44165) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44169 ∧
      t.getMem 29296 = 0 ∧ t.getMem 29304 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 29296 ∨ A = 29304) := by
  refine ⟨_, symRun_sound zero39Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero39Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero39Run.res, rv_simp]
  · simp [zero39Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero39Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero39_spec

def zero13Words : List (BitVec 32) := [0x7f37,0xd0f0f13,0xf3023,0xf3423]
sym_block zero13Run := symRun { noAlias := true } zero13Words (pcOf 44180) 20

theorem zero13_spec {im : Image} (hc : CodeAt im (pcOf 44180) zero13Words)
    (s : MachineState) (hpc : s.pc = pcOf 44180) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 44184 ∧
      t.getMem 28880 = 0 ∧ t.getMem 28888 = 0 ∧
      RegsExcept s t [.x30] ∧ Frame s t (fun A => A = 28880 ∨ A = 28888) := by
  refine ⟨_, symRun_sound zero13Run hc s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [zero13Run.res, rv_simp, accessValid_iff, MEMORY_BYTES]
  · rfl
  · simp [zero13Run.res, rv_simp]
  · simp [zero13Run.res, rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, zero13Run.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by omega), if_neg (by omega)]

#print axioms zero13_spec

def cleanupWords : List (BitVec 32) := [0x313,0x393,0x713,0x793,0xe13,0xe93,0xf13,0xd89d406f]
sym_block cleanupRun := symRun { noAlias := true } cleanupWords (pcOf 44184) 20

theorem cleanup_spec {im : Image} (hc : CodeAt im (pcOf 44184) cleanupWords)
    (s : MachineState) (hpc : s.pc = pcOf 44184) :
    ∃ t, Steps im s 8 8 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound cleanupRun hc s hpc ?_, ?_, ?_, ?_, ?_⟩
  · simp [cleanupRun.res, rv_simp]
  · rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A _ _; rfl

#print axioms cleanup_spec

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

theorem tail_full {im : Image} (hc : CodeAt im (pcOf prologueBase) tailWords)
    (s : MachineState) (hpc : s.pc = pcOf prologueBase) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf (prologueBase + 10) ∧
      t.getReg .x6 = s.getMem 0x8470 ∧
      t.getReg .x7 = (s.getMem 0x8478 <<< 16) >>> 16 ∧
      t.getReg .x28 = s.getMem 0x8478 >>> 48 ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = s.getMem 0x8478 >>> 48 ∧
      RegsExcept s t [.x6,.x7,.x28,.x29,.x30] ∧
      Frame s t (fun A => A = policyAddress) := by
  refine ⟨_, symRun_sound tailRun hc s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [tailRun.res, rv_simp, accessValid_iff, MEMORY_BYTES, prologueBase, policyAddress]
  · rfl
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getReg, tailRun.res]; t3n []
  · simp only [Result.toState_getMem, tailRun.res]; t3n [policyAddress]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hne
    simp only [Result.toState_getMem, tailRun.res]
    t3n [policyAddress]
    rw [Nat.mod_eq_of_lt (show A < 18446744073709551616 by simpa using hA),
      if_neg (by simpa [policyAddress] using hne)]

structure AdapterCodeAt (im : Image) : Prop where
  tail : CodeAt im (pcOf 44096) tailWords
  guard : CodeAt im (pcOf 44106) guardWords
  mainHighSetup : CodeAt im (pcOf 44109) mainHighSetupWords
  mainHighLoop : CodeAt im (pcOf 44115) copyWords
  middleSetup : CodeAt im (pcOf 44124) middleSetupWords
  middleLoop : CodeAt im (pcOf 44130) copyWords
  pair3Setup : CodeAt im (pcOf 44139) pair3SetupWords
  pair3Loop : CodeAt im (pcOf 44145) copyWords
  pair2Setup : CodeAt im (pcOf 44154) pair2SetupWords
  pair2Loop : CodeAt im (pcOf 44160) copyWords
  pair1Setup : CodeAt im (pcOf 44169) pair1SetupWords
  pair1Loop : CodeAt im (pcOf 44175) copyWords
  restoreTail : CodeAt im (pcOf 44120) restoreTailWords
  zero91 : CodeAt im (pcOf 44135) zero91Words
  zero65 : CodeAt im (pcOf 44150) zero65Words
  zero39 : CodeAt im (pcOf 44165) zero39Words
  zero13 : CodeAt im (pcOf 44180) zero13Words
  cleanup : CodeAt im (pcOf 44184) cleanupWords

theorem adapter_spec {im : Image} (hc : AdapterCodeAt im)
    (s : MachineState) (hpc : s.pc = pcOf 44096)
    (H : Nat) (hH : H < 5832) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3211 3211 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      t.getMem 31600 = s.getMem 33904 ∧
      t.getMem 31608 = (s.getMem 33912 <<< 16) >>> 16 ∧
      (∀ i, i ≤ 295 → t.getMem (BitVec.ofNat 64 (31616 + 8 * i)) = s.getMem (BitVec.ofNat 64 (31536 + 8 * i))) ∧
      (∀ i, i ≤ 181 → t.getMem (BitVec.ofNat 64 (30144 + 8 * i)) = s.getMem (BitVec.ofNat 64 (30080 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29728 + 8 * i)) = s.getMem (BitVec.ofNat 64 (29680 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (29312 + 8 * i)) = s.getMem (BitVec.ofNat 64 (29280 + 8 * i))) ∧
      (∀ i, i ≤ 49 → t.getMem (BitVec.ofNat 64 (28896 + 8 * i)) = s.getMem (BitVec.ofNat 64 (28880 + 8 * i))) ∧
      t.getMem 30128 = 0 ∧ t.getMem 30136 = 0 ∧
      t.getMem 29712 = 0 ∧ t.getMem 29720 = 0 ∧
      t.getMem 29296 = 0 ∧ t.getMem 29304 = 0 ∧
      t.getMem 28880 = 0 ∧ t.getMem 28888 = 0 ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨s1, st1, pc1, x61, x71, x281, meta1, r1, f1⟩ := tail_full hc.tail s hpc
  obtain ⟨s2, st2, pc2, r2, f2⟩ := guard_spec hc.guard s1 pc1 H (by omega) (x281.trans hh)
  rw [if_pos hH] at pc2
  obtain ⟨s3, st3, pc3, m3, r3, f3⟩ := mainHigh_move hc.mainHighSetup hc.mainHighLoop s2 pc2
  obtain ⟨s4, st4, pc4, m4a, m4b, r4, f4⟩ := restoreTail_spec hc.restoreTail s3 pc3
  obtain ⟨s5, st5, pc5, m5, r5, f5⟩ := middle_move hc.middleSetup hc.middleLoop s4 pc4
  obtain ⟨s6, st6, pc6, m6a, m6b, r6, f6⟩ := zero91_spec hc.zero91 s5 pc5
  obtain ⟨s7, st7, pc7, m7, r7, f7⟩ := pair3_move hc.pair3Setup hc.pair3Loop s6 pc6
  obtain ⟨s8, st8, pc8, m8a, m8b, r8, f8⟩ := zero65_spec hc.zero65 s7 pc7
  obtain ⟨s9, st9, pc9, m9, r9, f9⟩ := pair2_move hc.pair2Setup hc.pair2Loop s8 pc8
  obtain ⟨s10, st10, pc10, m10a, m10b, r10, f10⟩ := zero39_spec hc.zero39 s9 pc9
  obtain ⟨s11, st11, pc11, m11, r11, f11⟩ := pair1_move hc.pair1Setup hc.pair1Loop s10 pc10
  obtain ⟨s12, st12, pc12, m12a, m12b, r12, f12⟩ := zero13_spec hc.zero13 s11 pc11
  obtain ⟨t, st13, pc13, zeros, r13, f13⟩ := cleanup_spec hc.cleanup s12 pc12
  change s4.getMem (BitVec.ofNat 64 31600) = _ at m4a
  change s4.getMem (BitVec.ofNat 64 31608) = _ at m4b
  change s6.getMem (BitVec.ofNat 64 30128) = _ at m6a
  change s6.getMem (BitVec.ofNat 64 30136) = _ at m6b
  change s8.getMem (BitVec.ofNat 64 29712) = _ at m8a
  change s8.getMem (BitVec.ofNat 64 29720) = _ at m8b
  change s10.getMem (BitVec.ofNat 64 29296) = _ at m10a
  change s10.getMem (BitVec.ofNat 64 29304) = _ at m10b
  change s12.getMem (BitVec.ofNat 64 28880) = _ at m12a
  change s12.getMem (BitVec.ofNat 64 28888) = _ at m12b
  refine ⟨t, ?_, pc13, zeros, ?_, ?_, ?_, ?_, ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ , ?_ ⟩
  · exact ((((((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans st10).trans st11).trans st12).trans st13)
  · exact ((((((((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).trans r7).trans r8).trans r9).trans r10).trans r11).trans r12).trans r13).mono (by decide)
  · rw [f13 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 policyAddress (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), meta1, hh]
  · change t.getMem (BitVec.ofNat 64 31600) = _
    rw [f13 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 31600 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m4a, r3.get (by decide), r2.get (by decide), x61]
  · change t.getMem (BitVec.ofNat 64 31608) = _
    rw [f13 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 31608 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m4b, r3.get (by decide), r2.get (by decide), x71]
  · intro i hi
    rw [f13 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (31616 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m3 i hi, f2 (31536 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (31536 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (30144 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m5 i hi, f4 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (30080 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (29728 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m7 i hi, f6 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (29680 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 (29312 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m9 i hi, f8 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (29280 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · intro i hi
    rw [f13 (28896 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 (28896 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m11 i hi, f10 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f6 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f5 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f4 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f3 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f2 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f1 (28880 + 8 * i) (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega)]
  · change t.getMem (BitVec.ofNat 64 30128) = _
    rw [f13 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 30128 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m6a]
  · change t.getMem (BitVec.ofNat 64 30136) = _
    rw [f13 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f8 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f7 30136 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m6b]
  · change t.getMem (BitVec.ofNat 64 29712) = _
    rw [f13 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 29712 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m8a]
  · change t.getMem (BitVec.ofNat 64 29720) = _
    rw [f13 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f10 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f9 29720 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m8b]
  · change t.getMem (BitVec.ofNat 64 29296) = _
    rw [f13 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29296 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m10a]
  · change t.getMem (BitVec.ofNat 64 29304) = _
    rw [f13 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f12 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), f11 29304 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m10b]
  · change t.getMem (BitVec.ofNat 64 28880) = _
    rw [f13 28880 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m12a]
  · change t.getMem (BitVec.ofNat 64 28888) = _
    rw [f13 28888 (by norm_num [policyAddress] <;> omega) (by norm_num [policyAddress] <;> omega), m12b]
  · exact ((((((((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans f7).trans f8).trans f9).trans f10).trans f11).trans f12).trans f13).mono (by intro A _ h; dsimp [policyAddress] at h ⊢; rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) <;> first | exact False.elim h | omega)

#print axioms adapter_spec
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
def adapterLayout : SigGolfCandidate.Rv.Layout := [(0, tailWords), (10, guardWords), (13, mainHighSetupWords), (19, copyWords), (24, restoreTailWords), (28, middleSetupWords), (34, copyWords), (39, zero91Words), (43, pair3SetupWords), (49, copyWords), (54, zero65Words), (58, pair2SetupWords), (64, copyWords), (69, zero39Words), (73, pair1SetupWords), (79, copyWords), (84, zero13Words), (88, cleanupWords), (96, [0xb08d506f])]

theorem adapterLayout_ok : layoutOk 0 adapterLayout = true := by decide +kernel

theorem adapterLayout_code : layoutCode adapterLayout = prologueWords := by decide +kernel

theorem adapter_codeAt {im : Image} (hc : CodeAt im (pcOf 44096) prologueWords) :
    AdapterCodeAt im := by
  have hl : CodeAt im (pcOf 44096) (layoutCode adapterLayout) := by
    rw [adapterLayout_code]; exact hc
  constructor
  · exact codeAt_sublayout hl adapterLayout_ok (i := 0) (o := 0) (seg := tailWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 1) (o := 10) (seg := guardWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 2) (o := 13) (seg := mainHighSetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 3) (o := 19) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 5) (o := 28) (seg := middleSetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 6) (o := 34) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 8) (o := 43) (seg := pair3SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 9) (o := 49) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 11) (o := 58) (seg := pair2SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 12) (o := 64) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 14) (o := 73) (seg := pair1SetupWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 15) (o := 79) (seg := copyWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 4) (o := 24) (seg := restoreTailWords) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 7) (o := 39) (seg := zero91Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 10) (o := 54) (seg := zero65Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 13) (o := 69) (seg := zero39Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 16) (o := 84) (seg := zero13Words) (by decide +kernel)
  · exact codeAt_sublayout hl adapterLayout_ok (i := 17) (o := 88) (seg := cleanupWords) (by decide +kernel)

#print axioms adapter_codeAt

end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

def serializedWord (read : Nat → Word) (k : Nat) : Word :=
  if k < 26 then read k else if k < 28 then 0 else
  if k < 78 then read (k - 2) else if k < 80 then 0 else
  if k < 130 then read (k - 4) else if k < 132 then 0 else
  if k < 182 then read (k - 6) else if k < 184 then 0 else
  if k < 366 then read (k - 8) else if k = 366 then read 654 else
  if k = 367 then (read 655 <<< 16) >>> 16 else read (k - 10)

theorem adapter_readout {im : Image} (hc : AdapterCodeAt im)
    (s : MachineState) (hpc : s.pc = pcOf 44096)
    (H : Nat) (hH : H < 5832) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3211 3211 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      (∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * k)) =
        serializedWord (fun j => s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))) k) ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨t, steps, pc, zregs, regs, hints, low, high, main, middle, pair3, pair2, pair1,
    z91a, z91b, z65a, z65b, z39a, z39b, z13a, z13b, frame⟩ := adapter_spec hc s hpc H hH hh
  refine ⟨t, steps, pc, zregs, regs, hints, ?_, frame⟩
  intro k hk
  unfold serializedWord
  split_ifs with h26 h28 h78 h80 h130 h132 h182 h184 h366 he366 he367
  · exact frame (0x7000 + 8 * k) (by omega) (by dsimp [policyAddress]; omega)
  · have e : k = 26 ∨ k = 27 := by omega
    rcases e with rfl | rfl
    · exact z13a
    · exact z13b
  · rw [show 0x7000 + 8 * k = 28896 + 8 * (k - 28) by omega,
      pair1 (k - 28) (by omega)]
    congr 2
    omega
  · have e : k = 78 ∨ k = 79 := by omega
    rcases e with rfl | rfl
    · exact z39a
    · exact z39b
  · rw [show 0x7000 + 8 * k = 29312 + 8 * (k - 80) by omega,
      pair2 (k - 80) (by omega)]
    congr 2
    omega
  · have e : k = 130 ∨ k = 131 := by omega
    rcases e with rfl | rfl
    · exact z65a
    · exact z65b
  · rw [show 0x7000 + 8 * k = 29728 + 8 * (k - 132) by omega,
      pair3 (k - 132) (by omega)]
    congr 2
    omega
  · have e : k = 182 ∨ k = 183 := by omega
    rcases e with rfl | rfl
    · exact z91a
    · exact z91b
  · rw [show 0x7000 + 8 * k = 30144 + 8 * (k - 184) by omega,
      middle (k - 184) (by omega)]
    congr 2
    omega
  · subst k; exact low
  · subst k; exact high
  · rw [show 0x7000 + 8 * k = 31616 + 8 * (k - 368) by omega,
      main (k - 368) (by omega)]
    congr 2
    omega

#print axioms adapter_readout

end ClaudeWCT.W9.Machine.Expand.SharedCompact


namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M

def entryWord : BitVec 32 := 0x1002b06f

theorem entry_step {im : Image} (hc : CodeAt im (pcOf 0) [entryWord])
    (s : MachineState) (hpc : s.pc = pcOf 0) :
    Steps im s 1 1 (s.setPC (pcOf 44096)) := by
  obtain ⟨imm, hd, hoff⟩ := jalTo_sound (show jalTo entryWord 0 = some 44096 by decide +kernel)
  exact jal_x0_step hc hd hoff s hpc

theorem front_readout {im : Image} (he : CodeAt im (pcOf 0) [entryWord])
    (hc : AdapterCodeAt im) (s : MachineState) (hpc : s.pc = pcOf 0)
    (H : Nat) (hH : H < 5832) (hh : s.getMem 0x8478 >>> 48 = BitVec.ofNat 64 H) :
    ∃ t, Steps im s 3212 3212 t ∧ t.pc = pcOf 1 ∧
      (∀ r ∈ [.x6,.x7,.x14,.x15,.x28,.x29,.x30], t.getReg r = 0) ∧
      RegsExcept s t [.x6,.x7,.x14,.x15,.x28,.x29,.x30] ∧
      t.getMem (BitVec.ofNat 64 policyAddress) = BitVec.ofNat 64 H ∧
      (∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * k)) =
        serializedWord (fun j => s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))) k) ∧
      Frame s t (fun A => A = policyAddress ∨ (0x70d0 ≤ A ∧ A < 0x84c0)) := by
  obtain ⟨t, st, pc, zeros, regs, hints, mem, frame⟩ :=
    adapter_readout hc (s.setPC (pcOf 44096)) rfl H hH hh
  exact ⟨t, (entry_step he s hpc).trans st, pc, zeros, regs, hints, mem, frame⟩

#print axioms front_readout
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3M SigGolfCandidate.Rv

theorem installed_adapter_codeAt : AdapterCodeAt Images.expandImage := by
  apply adapter_codeAt
  apply codeAt_expand_current_chunk
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem installed_entry_codeAt : CodeAt Images.expandImage (pcOf 0) [entryWord] := by
  apply codeAt_expand_current_chunk
  · decide +kernel
  · decide +kernel
  · decide +kernel
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
abbrev destination (region slot child : Nat) : Nat :=
  region + 16 * slot + 48 * (1 - child % 2)

def pathCode0 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x85313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x608b303,0x688b383,0x6e3023,0x7e3423]
sym_block path0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
theorem path0_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path0.res.st.obl := by
  rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
  all_goals
    simp only [path0.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit]
    norm_num
    omega
#print axioms path0_obligs
theorem path0_steps {im : Image} (hc : CodeAt im (pcOf 45307) pathCode0)
    (s : MachineState) (hp : s.pc = pcOf 45307) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45320 ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child)) =
        s.getMem (BitVec.ofNat 64 (source + 96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot child ∨
        A = destination region slot child + 8) := by
  have ho := path0_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound path0 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
#print axioms path0_steps

def pathCode1 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x185313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x708b303,0x788b383,0x6e3023,0x7e3423]
sym_block path1 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
theorem path1_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
  all_goals
    simp only [path1.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path1_obligs
theorem path1_steps {im : Image} (hc : CodeAt im (pcOf 45321) pathCode1)
    (s : MachineState) (hp : s.pc = pcOf 45321) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45334 ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2))) =
        s.getMem (BitVec.ofNat 64 (source + 112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 2) ∨
        A = destination region slot (child / 2) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path1_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound path1 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
#print axioms path1_steps

def pathCode2 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x285313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x808b303,0x888b383,0x6e3023,0x7e3423]
sym_block path2 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
theorem path2_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
  all_goals
    simp only [path2.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path2_obligs
theorem path2_steps {im : Image} (hc : CodeAt im (pcOf 45335) pathCode2)
    (s : MachineState) (hp : s.pc = pcOf 45335) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45348 ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4))) =
        s.getMem (BitVec.ofNat 64 (source + 128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 4) ∨
        A = destination region slot (child / 4) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path2_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound path2 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
#print axioms path2_steps

def pathCode3 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x385313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0x908b303,0x988b383,0x6e3023,0x7e3423]
sym_block path3 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
theorem path3_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
  all_goals
    simp only [path3.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path3_obligs
theorem path3_steps {im : Image} (hc : CodeAt im (pcOf 45349) pathCode3)
    (s : MachineState) (hp : s.pc = pcOf 45349) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45362 ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8))) =
        s.getMem (BitVec.ofNat 64 (source + 144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 8) ∨
        A = destination region slot (child / 8) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path3_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound path3 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
#print axioms path3_steps

def pathCode4 : List (BitVec 32) := [0x4e1e13,0x8e0e33,0x485313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xa08b303,0xa88b383,0x6e3023,0x7e3423]
sym_block path4 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
theorem path4_obligs (s : MachineState) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    Oblig.all s path4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
  all_goals
    simp only [path4.res]
    t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms path4_obligs
theorem path4_steps {im : Image} (hc : CodeAt im (pcOf 45363) pathCode4)
    (s : MachineState) (hp : s.pc = pcOf 45363) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45376 ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16))) =
        s.getMem (BitVec.ofNat 64 (source + 160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 16) ∨
        A = destination region slot (child / 16) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path4_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound path4 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
#print axioms path4_steps

end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block rebased0_0 := symRun { noAlias := true } pathCode0 (pcOf 45307) 100
sym_block rebased0_1 := symRun { noAlias := true } pathCode0 (pcOf 45441) 100
sym_block rebased0_2 := symRun { noAlias := true } pathCode0 (pcOf 45584) 100
sym_block rebased0_3 := symRun { noAlias := true } pathCode0 (pcOf 45718) 100
sym_block rebased0_4 := symRun { noAlias := true } pathCode0 (pcOf 45861) 100
sym_block rebased0_5 := symRun { noAlias := true } pathCode0 (pcOf 45995) 100
sym_block rebased0_6 := symRun { noAlias := true } pathCode0 (pcOf 46138) 100
sym_block rebased0_7 := symRun { noAlias := true } pathCode0 (pcOf 46272) 100
sym_block rebased0_8 := symRun { noAlias := true } pathCode0 (pcOf 46417) 100
theorem run_path0 {b : Nat} (hb : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) :
    symRun { noAlias := true } pathCode0 (pcOf b) 100 =
      some ⟨path0.res.st, .c (pcOf (b + 13)), path0.res.stop, path0.res.steps, path0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased0_0.trans (congrArg some (by kernel_rfl))
  · exact rebased0_1.trans (congrArg some (by kernel_rfl))
  · exact rebased0_2.trans (congrArg some (by kernel_rfl))
  · exact rebased0_3.trans (congrArg some (by kernel_rfl))
  · exact rebased0_4.trans (congrArg some (by kernel_rfl))
  · exact rebased0_5.trans (congrArg some (by kernel_rfl))
  · exact rebased0_6.trans (congrArg some (by kernel_rfl))
  · exact rebased0_7.trans (congrArg some (by kernel_rfl))
  · exact rebased0_8.trans (congrArg some (by kernel_rfl))
theorem path0_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45307 ∨ b = 45441 ∨ b = 45584 ∨ b = 45718 ∨ b = 45861 ∨ b = 45995 ∨ b = 46138 ∨ b = 46272 ∨ b = 46417) (hc : CodeAt im (pcOf b) pathCode0)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child)) =
        s.getMem (BitVec.ofNat 64 (source + 96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot child ∨
        A = destination region slot child + 8) := by
  have ho := path0_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path0 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one child with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path0.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_and1,hbit,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path0_steps_rebased
sym_block rebased1_0 := symRun { noAlias := true } pathCode1 (pcOf 45321) 100
sym_block rebased1_1 := symRun { noAlias := true } pathCode1 (pcOf 45455) 100
sym_block rebased1_2 := symRun { noAlias := true } pathCode1 (pcOf 45598) 100
sym_block rebased1_3 := symRun { noAlias := true } pathCode1 (pcOf 45732) 100
sym_block rebased1_4 := symRun { noAlias := true } pathCode1 (pcOf 45875) 100
sym_block rebased1_5 := symRun { noAlias := true } pathCode1 (pcOf 46009) 100
sym_block rebased1_6 := symRun { noAlias := true } pathCode1 (pcOf 46152) 100
sym_block rebased1_7 := symRun { noAlias := true } pathCode1 (pcOf 46286) 100
sym_block rebased1_8 := symRun { noAlias := true } pathCode1 (pcOf 46431) 100
theorem run_path1 {b : Nat} (hb : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) :
    symRun { noAlias := true } pathCode1 (pcOf b) 100 =
      some ⟨path1.res.st, .c (pcOf (b + 13)), path1.res.stop, path1.res.steps, path1.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased1_0.trans (congrArg some (by kernel_rfl))
  · exact rebased1_1.trans (congrArg some (by kernel_rfl))
  · exact rebased1_2.trans (congrArg some (by kernel_rfl))
  · exact rebased1_3.trans (congrArg some (by kernel_rfl))
  · exact rebased1_4.trans (congrArg some (by kernel_rfl))
  · exact rebased1_5.trans (congrArg some (by kernel_rfl))
  · exact rebased1_6.trans (congrArg some (by kernel_rfl))
  · exact rebased1_7.trans (congrArg some (by kernel_rfl))
  · exact rebased1_8.trans (congrArg some (by kernel_rfl))
theorem path1_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45321 ∨ b = 45455 ∨ b = 45598 ∨ b = 45732 ∨ b = 45875 ∨ b = 46009 ∨ b = 46152 ∨ b = 46286 ∨ b = 46431) (hc : CodeAt im (pcOf b) pathCode1)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2))) =
        s.getMem (BitVec.ofNat 64 (source + 112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 2) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 2) ∨
        A = destination region slot (child / 2) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path1_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path1 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 2) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path1.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path1_steps_rebased
sym_block rebased2_0 := symRun { noAlias := true } pathCode2 (pcOf 45335) 100
sym_block rebased2_1 := symRun { noAlias := true } pathCode2 (pcOf 45469) 100
sym_block rebased2_2 := symRun { noAlias := true } pathCode2 (pcOf 45612) 100
sym_block rebased2_3 := symRun { noAlias := true } pathCode2 (pcOf 45746) 100
sym_block rebased2_4 := symRun { noAlias := true } pathCode2 (pcOf 45889) 100
sym_block rebased2_5 := symRun { noAlias := true } pathCode2 (pcOf 46023) 100
sym_block rebased2_6 := symRun { noAlias := true } pathCode2 (pcOf 46166) 100
sym_block rebased2_7 := symRun { noAlias := true } pathCode2 (pcOf 46300) 100
sym_block rebased2_8 := symRun { noAlias := true } pathCode2 (pcOf 46445) 100
theorem run_path2 {b : Nat} (hb : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) :
    symRun { noAlias := true } pathCode2 (pcOf b) 100 =
      some ⟨path2.res.st, .c (pcOf (b + 13)), path2.res.stop, path2.res.steps, path2.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased2_0.trans (congrArg some (by kernel_rfl))
  · exact rebased2_1.trans (congrArg some (by kernel_rfl))
  · exact rebased2_2.trans (congrArg some (by kernel_rfl))
  · exact rebased2_3.trans (congrArg some (by kernel_rfl))
  · exact rebased2_4.trans (congrArg some (by kernel_rfl))
  · exact rebased2_5.trans (congrArg some (by kernel_rfl))
  · exact rebased2_6.trans (congrArg some (by kernel_rfl))
  · exact rebased2_7.trans (congrArg some (by kernel_rfl))
  · exact rebased2_8.trans (congrArg some (by kernel_rfl))
theorem path2_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45335 ∨ b = 45469 ∨ b = 45612 ∨ b = 45746 ∨ b = 45889 ∨ b = 46023 ∨ b = 46166 ∨ b = 46300 ∨ b = 46445) (hc : CodeAt im (pcOf b) pathCode2)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4))) =
        s.getMem (BitVec.ofNat 64 (source + 128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 4) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 4) ∨
        A = destination region slot (child / 4) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path2_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path2 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 4) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path2.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path2_steps_rebased
sym_block rebased3_0 := symRun { noAlias := true } pathCode3 (pcOf 45349) 100
sym_block rebased3_1 := symRun { noAlias := true } pathCode3 (pcOf 45483) 100
sym_block rebased3_2 := symRun { noAlias := true } pathCode3 (pcOf 45626) 100
sym_block rebased3_3 := symRun { noAlias := true } pathCode3 (pcOf 45760) 100
sym_block rebased3_4 := symRun { noAlias := true } pathCode3 (pcOf 45903) 100
sym_block rebased3_5 := symRun { noAlias := true } pathCode3 (pcOf 46037) 100
sym_block rebased3_6 := symRun { noAlias := true } pathCode3 (pcOf 46180) 100
sym_block rebased3_7 := symRun { noAlias := true } pathCode3 (pcOf 46314) 100
sym_block rebased3_8 := symRun { noAlias := true } pathCode3 (pcOf 46459) 100
theorem run_path3 {b : Nat} (hb : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) :
    symRun { noAlias := true } pathCode3 (pcOf b) 100 =
      some ⟨path3.res.st, .c (pcOf (b + 13)), path3.res.stop, path3.res.steps, path3.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased3_0.trans (congrArg some (by kernel_rfl))
  · exact rebased3_1.trans (congrArg some (by kernel_rfl))
  · exact rebased3_2.trans (congrArg some (by kernel_rfl))
  · exact rebased3_3.trans (congrArg some (by kernel_rfl))
  · exact rebased3_4.trans (congrArg some (by kernel_rfl))
  · exact rebased3_5.trans (congrArg some (by kernel_rfl))
  · exact rebased3_6.trans (congrArg some (by kernel_rfl))
  · exact rebased3_7.trans (congrArg some (by kernel_rfl))
  · exact rebased3_8.trans (congrArg some (by kernel_rfl))
theorem path3_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45349 ∨ b = 45483 ∨ b = 45626 ∨ b = 45760 ∨ b = 45903 ∨ b = 46037 ∨ b = 46180 ∨ b = 46314 ∨ b = 46459) (hc : CodeAt im (pcOf b) pathCode3)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8))) =
        s.getMem (BitVec.ofNat 64 (source + 144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 8) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 8) ∨
        A = destination region slot (child / 8) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path3_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path3 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 8) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path3.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path3_steps_rebased
sym_block rebased4_0 := symRun { noAlias := true } pathCode4 (pcOf 45363) 100
sym_block rebased4_1 := symRun { noAlias := true } pathCode4 (pcOf 45497) 100
sym_block rebased4_2 := symRun { noAlias := true } pathCode4 (pcOf 45640) 100
sym_block rebased4_3 := symRun { noAlias := true } pathCode4 (pcOf 45774) 100
sym_block rebased4_4 := symRun { noAlias := true } pathCode4 (pcOf 45917) 100
sym_block rebased4_5 := symRun { noAlias := true } pathCode4 (pcOf 46051) 100
sym_block rebased4_6 := symRun { noAlias := true } pathCode4 (pcOf 46194) 100
sym_block rebased4_7 := symRun { noAlias := true } pathCode4 (pcOf 46328) 100
sym_block rebased4_8 := symRun { noAlias := true } pathCode4 (pcOf 46473) 100
theorem run_path4 {b : Nat} (hb : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) :
    symRun { noAlias := true } pathCode4 (pcOf b) 100 =
      some ⟨path4.res.st, .c (pcOf (b + 13)), path4.res.stop, path4.res.steps, path4.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rebased4_0.trans (congrArg some (by kernel_rfl))
  · exact rebased4_1.trans (congrArg some (by kernel_rfl))
  · exact rebased4_2.trans (congrArg some (by kernel_rfl))
  · exact rebased4_3.trans (congrArg some (by kernel_rfl))
  · exact rebased4_4.trans (congrArg some (by kernel_rfl))
  · exact rebased4_5.trans (congrArg some (by kernel_rfl))
  · exact rebased4_6.trans (congrArg some (by kernel_rfl))
  · exact rebased4_7.trans (congrArg some (by kernel_rfl))
  · exact rebased4_8.trans (congrArg some (by kernel_rfl))
theorem path4_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45363 ∨ b = 45497 ∨ b = 45640 ∨ b = 45774 ∨ b = 45917 ∨ b = 46051 ∨ b = 46194 ∨ b = 46328 ∨ b = 46473) (hc : CodeAt im (pcOf b) pathCode4)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128) (hb : slot < 53)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 slot) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b + 13) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16))) =
        s.getMem (BitVec.ofNat 64 (source + 160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child / 16) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region slot (child / 16) ∨
        A = destination region slot (child / 16) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := path4_obligs s region source child slot hr0 hr1 hra hs0 hs1 hsa hj hb h8 h16 h17 h28
  refine ⟨_, symRun_sound (run_path4 hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [path4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [path4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 16) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,path4.res]
      t3n [h8,h16,h17,h28,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      split_ifs <;> (first | rfl | omega)

#print axioms path4_steps_rebased
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Load one validated path-plan byte without changing the source or witness memory. -/
theorem load_plan_step {im : Image} {w : BitVec 32} (pc : Word)
    (hc : CodeAt im pc [w]) (level : Fin 5)
    (hd : decodeInstruction w = some (.base (.LBU .x28 .x18 (BitVec.ofNat 12 level.val))))
    (s : MachineState) (hp : s.pc = pc) (table slot : Nat)
    (ht : table + 5 < 2^24) (hs : slot < 53)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table + level.val)) = BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pc + 4 ∧
      t.getReg .x28 = BitVec.ofNat 64 slot ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hoff : signExtend12 (BitVec.ofNat 12 level.val) = BitVec.ofNat 64 level.val := by
    fin_cases level <;> decide +kernel
  have haddr : s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val) =
      BitVec.ofNat 64 (table + level.val) := by rw [h18, hoff, ofNat_add_ofNat]
  have hv : accessValid (s.getReg .x18 + signExtend12 (BitVec.ofNat 12 level.val)) 1 = true := by
    rw [haddr]; simp only [accessValid_iff, BitVec.toNat_ofNat, MEMORY_BYTES]
    have := level.isLt
    omega
  have hz : (BitVec.ofNat 8 slot).zeroExtend 64 = BitVec.ofNat 64 slot := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have st := steps_lbu hc hp hd hv
  rw [haddr, hbyte, hz] at st
  refine ⟨_, st, ?_, ?_, ?_, ?_⟩
  · change s.pc + 4 = pc + 4; rw [hp]
  · rfl
  · intro r hr; simp at hr; cases r <;> simp_all [MachineState.setReg, MachineState.getReg, MachineState.setPC]
  · intro A hA hn; simp [rv_simp]
#print axioms load_plan_step
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def sixthCode : List (BitVec 32) := [0x34000e13,0x8e0e33,0x585313,0x137313,0x100393,0x40638333,0x3000393,0x2730333,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block sixth := symRun { noAlias := true } sixthCode (pcOf 45510) 100
theorem sixth_obligs (s : MachineState) (region source child : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s sixth.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [sixth.res]
    t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms sixth_obligs
theorem sixth_steps {im : Image} (hc : CodeAt im (pcOf 45510) sixthCode)
    (s : MachineState) (hp : s.pc = pcOf 45510) (region source child : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf 45523 ∧
      t.getMem (BitVec.ofNat 64 (destination region 52 (child / 32))) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (destination region 52 (child / 32) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region 52 (child / 32) ∨
        A = destination region 52 (child / 32) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := sixth_obligs s region source child hr0 hr1 hra hs0 hs1 hsa hj h8 h16 h17
  refine ⟨_, symRun_sound sixth hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [sixth.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · intro r hr; simp at hr; cases r <;> simp_all [sixth.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
#print axioms sixth_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
private theorem low_slot_sub : (1264#64 - 48#64) = 1216#64 := rfl

abbrev topDest0 (child : Nat) : Nat := 7808 + 576 * (child / 32 % 2)
def topCode0 : List (BitVec 32) := [0x585313,0x137313,0x24000393,0x2730333,0x2e37,0xe80e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top0 := symRun { noAlias := true } topCode0 (pcOf 45376) 100
theorem top0_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top0.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top0.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top0_obligs
theorem top0_steps {im : Image} (hc : CodeAt im (pcOf 45376) topCode0)
    (s : MachineState) (hp : s.pc = pcOf 45376) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45387 ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest0 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest0 child ∨
        A = topDest0 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top0_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top0 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top0.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top0.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top0.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest0]
      simp only [topDest0,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top0_steps


abbrev topDest1 (child : Nat) : Nat := 6912 + 576 * (child / 64 % 2)
def topCode1 : List (BitVec 32) := [0x685313,0x137313,0x24000393,0x2730333,0x2e37,0xb00e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top1 := symRun { noAlias := true } topCode1 (pcOf 45523) 100
theorem top1_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top1.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top1.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top1_obligs
theorem top1_steps {im : Image} (hc : CodeAt im (pcOf 45523) topCode1)
    (s : MachineState) (hp : s.pc = pcOf 45523) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45534 ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest1 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest1 child ∨
        A = topDest1 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top1_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top1 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top1.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top1.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top1.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest1]
      simp only [topDest1,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top1_steps


abbrev topDest2 (child : Nat) : Nat := 6016 + 576 * (child / 32 % 2)
def topCode2 : List (BitVec 32) := [0x585313,0x137313,0x24000393,0x2730333,0x1e37,0x780e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top2 := symRun { noAlias := true } topCode2 (pcOf 45653) 100
theorem top2_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top2.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top2.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top2_obligs
theorem top2_steps {im : Image} (hc : CodeAt im (pcOf 45653) topCode2)
    (s : MachineState) (hp : s.pc = pcOf 45653) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45664 ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest2 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest2 child ∨
        A = topDest2 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top2_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top2 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top2.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top2.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top2.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest2]
      simp only [topDest2,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top2_steps


abbrev topDest3 (child : Nat) : Nat := 5120 + 576 * (child / 64 % 2)
def topCode3 : List (BitVec 32) := [0x685313,0x137313,0x24000393,0x2730333,0x1e37,0x400e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top3 := symRun { noAlias := true } topCode3 (pcOf 45800) 100
theorem top3_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top3.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top3.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top3_obligs
theorem top3_steps {im : Image} (hc : CodeAt im (pcOf 45800) topCode3)
    (s : MachineState) (hp : s.pc = pcOf 45800) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45811 ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest3 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest3 child ∨
        A = topDest3 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top3_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top3 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top3.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top3.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top3.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest3]
      simp only [topDest3,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top3_steps


abbrev topDest4 (child : Nat) : Nat := 4224 + 576 * (child / 32 % 2)
def topCode4 : List (BitVec 32) := [0x585313,0x137313,0x24000393,0x2730333,0x1e37,0x80e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top4 := symRun { noAlias := true } topCode4 (pcOf 45930) 100
theorem top4_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top4.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top4.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top4_obligs
theorem top4_steps {im : Image} (hc : CodeAt im (pcOf 45930) topCode4)
    (s : MachineState) (hp : s.pc = pcOf 45930) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 45941 ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest4 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest4 child ∨
        A = topDest4 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top4_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top4 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top4.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top4.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top4.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest4]
      simp only [topDest4,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top4_steps


abbrev topDest5 (child : Nat) : Nat := 3328 + 576 * (child / 64 % 2)
def topCode5 : List (BitVec 32) := [0x685313,0x137313,0x24000393,0x2730333,0x1e37,0xd00e0e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top5 := symRun { noAlias := true } topCode5 (pcOf 46077) 100
theorem top5_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top5.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top5.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top5_obligs
theorem top5_steps {im : Image} (hc : CodeAt im (pcOf 46077) topCode5)
    (s : MachineState) (hp : s.pc = pcOf 46077) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46088 ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest5 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest5 child ∨
        A = topDest5 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top5_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top5 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top5.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top5.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top5.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest5]
      simp only [topDest5,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top5_steps


abbrev topDest6 (child : Nat) : Nat := 2432 + 576 * (child / 32 % 2)
def topCode6 : List (BitVec 32) := [0x585313,0x137313,0x24000393,0x2730333,0x1e37,0x980e0e13,0x6e0e33,0xb08b303,0xb88b383,0x6e3023,0x7e3423]
sym_block top6 := symRun { noAlias := true } topCode6 (pcOf 46207) 100
theorem top6_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top6.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
  all_goals
    simp only [top6.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top6_obligs
theorem top6_steps {im : Image} (hc : CodeAt im (pcOf 46207) topCode6)
    (s : MachineState) (hp : s.pc = pcOf 46207) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 11 14 t ∧ t.pc = pcOf 46218 ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child)) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (topDest6 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest6 child ∨
        A = topDest6 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top6_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top6 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top6.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top6.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top6.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest6]
      simp only [topDest6,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top6_steps


abbrev topDest7 (child : Nat) : Nat := 1536 + 576 * (child / 64 % 2)
def topCode7 : List (BitVec 32) := [0x685313,0x137313,0x24000393,0x2730333,0x60000e13,0x6e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top7 := symRun { noAlias := true } topCode7 (pcOf 46354) 100
theorem top7_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top7.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top7.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top7_obligs
theorem top7_steps {im : Image} (hc : CodeAt im (pcOf 46354) topCode7)
    (s : MachineState) (hp : s.pc = pcOf 46354) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46364 ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest7 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest7 child ∨
        A = topDest7 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top7_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top7 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top7.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top7.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top7.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest7]
      simp only [topDest7,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top7_steps


abbrev topDest8 (child : Nat) : Nat := 1264 - 48 * (child / 64 % 2)
def topCode8 : List (BitVec 32) := [0x685313,0x137313,0x3000393,0x2730333,0x4f000e13,0x406e0e33,0xc08b303,0xc88b383,0x6e3023,0x7e3423]
sym_block top8 := symRun { noAlias := true } topCode8 (pcOf 46499) 100
theorem top8_obligs (s : MachineState) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    Oblig.all s top8.res.st.obl := by
  have hj64 : child < 2^64 := by omega
  rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
  all_goals
    simp only [top8.res]
    t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64]
    norm_num
    omega
#print axioms top8_obligs
theorem top8_steps {im : Image} (hc : CodeAt im (pcOf 46499) topCode8)
    (s : MachineState) (hp : s.pc = pcOf 46499) (source child : Nat)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 10 13 t ∧ t.pc = pcOf 46509 ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child)) =
        s.getMem (BitVec.ofNat 64 (source + 192)) ∧
      t.getMem (BitVec.ofNat 64 (topDest8 child + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 200)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = topDest8 child ∨
        A = topDest8 child + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := top8_obligs s source child hs0 hs1 hsa hj h16 h17
  refine ⟨_, symRun_sound top8 hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [top8.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
  · intro r hr; simp at hr; cases r <;> simp_all [top8.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 64) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,top8.res]
      t3n [h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,topDest8]
      simp only [topDest8,hbit] at hn
      norm_num [low_slot_sub,rv_simp,ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals split_ifs <;> (first | rfl | omega)
#print axioms top8_steps


end ClaudeWCT.W9.Machine.Expand.SharedScatter


namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
sym_block sixthRebase0 := symRun { noAlias := true } sixthCode (pcOf 45510) 100
sym_block sixthRebase1 := symRun { noAlias := true } sixthCode (pcOf 45787) 100
sym_block sixthRebase2 := symRun { noAlias := true } sixthCode (pcOf 46064) 100
sym_block sixthRebase3 := symRun { noAlias := true } sixthCode (pcOf 46341) 100
sym_block sixthRebase4 := symRun { noAlias := true } sixthCode (pcOf 46486) 100
theorem run_sixth {b : Nat} (hb : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) :
    symRun { noAlias := true } sixthCode (pcOf b) 100 =
      some ⟨sixth.res.st, .c (pcOf (b + 13)), sixth.res.stop, sixth.res.steps, sixth.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact sixthRebase0.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase1.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase2.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase3.trans (congrArg some (by kernel_rfl))
  · exact sixthRebase4.trans (congrArg some (by kernel_rfl))
theorem sixth_steps_rebased {im : Image} {b : Nat} (hbpc : b = 45510 ∨ b = 45787 ∨ b = 46064 ∨ b = 46341 ∨ b = 46486) (hc : CodeAt im (pcOf b) sixthCode)
    (s : MachineState) (hp : s.pc = pcOf b) (region source child : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region % 8 = 0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source % 8 = 0)
    (hj : child < 128)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 region)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 child)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 source) :
    ∃ t, Steps im s 13 16 t ∧ t.pc = pcOf (b+13) ∧
      t.getMem (BitVec.ofNat 64 (destination region 52 (child / 32))) =
        s.getMem (BitVec.ofNat 64 (source + 176)) ∧
      t.getMem (BitVec.ofNat 64 (destination region 52 (child / 32) + 8)) =
        s.getMem (BitVec.ofNat 64 (source + 184)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A = destination region 52 (child / 32) ∨
        A = destination region 52 (child / 32) + 8) := by
  have hj64 : child < 2^64 := by omega
  have ho := sixth_obligs s region source child hr0 hr1 hra hs0 hs1 hsa hj h8 h16 h17
  refine ⟨_, symRun_sound (run_sixth hbpc) hc s hp ho, ?_,?_,?_,?_,?_⟩
  · simp [sixth.res, Result.toState_pc, E.eval, pcOf]
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))
  · intro r hr; simp at hr; cases r <;> simp_all [sixth.res,rv_simp] <;> rfl
  · intro A hA hn
    rcases Nat.mod_two_eq_zero_or_one (child / 32) with hbit | hbit
    all_goals
      simp only [Result.toState_getMem,sixth.res]
      t3n [h8,h16,h17,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,destination]
      simp only [destination,hbit] at hn
      norm_num [ofNat_shr child _ hj64,ofNat_and1,hbit,Nat.mod_eq_of_lt hj64,ofNat_add_ofNat,ofNat_eq_iff]
      all_goals first | rfl | (intro h; exfalso; omega) | (split_ifs <;> (first | rfl | omega))

#print axioms sixth_steps_rebased
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def value0Code : List (BitVec 32) := bv_list% 32 [0x8b303,0x88b383,0x2a643823,0x2a743c23]
sym_block value0_0 := symRun { noAlias := true } value0Code (pcOf 45266) 20
sym_block value0_1 := symRun { noAlias := true } value0Code (pcOf 45400) 20
sym_block value0_2 := symRun { noAlias := true } value0Code (pcOf 45543) 20
sym_block value0_3 := symRun { noAlias := true } value0Code (pcOf 45677) 20
sym_block value0_4 := symRun { noAlias := true } value0Code (pcOf 45820) 20
sym_block value0_5 := symRun { noAlias := true } value0Code (pcOf 45954) 20
sym_block value0_6 := symRun { noAlias := true } value0Code (pcOf 46097) 20
sym_block value0_7 := symRun { noAlias := true } value0Code (pcOf 46231) 20
sym_block value0_8 := symRun { noAlias := true } value0Code (pcOf 46376) 20
theorem value0_run {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) :
    symRun { noAlias := true } value0Code (pcOf b) 20 =
      some ⟨value0_0.res.st,.c (pcOf (b+4)),value0_0.res.stop,value0_0.res.steps,value0_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value0_0.trans (congrArg some (by kernel_rfl))
  · exact value0_1.trans (congrArg some (by kernel_rfl))
  · exact value0_2.trans (congrArg some (by kernel_rfl))
  · exact value0_3.trans (congrArg some (by kernel_rfl))
  · exact value0_4.trans (congrArg some (by kernel_rfl))
  · exact value0_5.trans (congrArg some (by kernel_rfl))
  · exact value0_6.trans (congrArg some (by kernel_rfl))
  · exact value0_7.trans (congrArg some (by kernel_rfl))
  · exact value0_8.trans (congrArg some (by kernel_rfl))
theorem value0_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hc : CodeAt im (pcOf b) value0Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 4 4 t ∧ t.pc=pcOf (b+4) ∧
      t.getMem (BitVec.ofNat 64 (region+688))=s.getMem (BitVec.ofNat 64 (source+0)) ∧
      t.getMem (BitVec.ofNat 64 (region+696))=s.getMem (BitVec.ofNat 64 (source+8)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+688 ∨ A=region+696) := by
  have ho : Oblig.all s value0_0.res.st.obl := by
    simp only [value0_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value0_run hb) hc s hp ho,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value0_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value0_steps
def value1Code : List (BitVec 32) := bv_list% 32 [0x108b303,0x188b383,0x26643823,0x26743c23,0x2e643023,0x2e743423]
sym_block value1_0 := symRun { noAlias := true } value1Code (pcOf 45270) 20
sym_block value1_1 := symRun { noAlias := true } value1Code (pcOf 45404) 20
sym_block value1_2 := symRun { noAlias := true } value1Code (pcOf 45547) 20
sym_block value1_3 := symRun { noAlias := true } value1Code (pcOf 45681) 20
sym_block value1_4 := symRun { noAlias := true } value1Code (pcOf 45824) 20
sym_block value1_5 := symRun { noAlias := true } value1Code (pcOf 45958) 20
sym_block value1_6 := symRun { noAlias := true } value1Code (pcOf 46101) 20
sym_block value1_7 := symRun { noAlias := true } value1Code (pcOf 46235) 20
sym_block value1_8 := symRun { noAlias := true } value1Code (pcOf 46380) 20
theorem value1_run {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380) :
    symRun { noAlias := true } value1Code (pcOf b) 20 =
      some ⟨value1_0.res.st,.c (pcOf (b+6)),value1_0.res.stop,value1_0.res.steps,value1_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value1_0.trans (congrArg some (by kernel_rfl))
  · exact value1_1.trans (congrArg some (by kernel_rfl))
  · exact value1_2.trans (congrArg some (by kernel_rfl))
  · exact value1_3.trans (congrArg some (by kernel_rfl))
  · exact value1_4.trans (congrArg some (by kernel_rfl))
  · exact value1_5.trans (congrArg some (by kernel_rfl))
  · exact value1_6.trans (congrArg some (by kernel_rfl))
  · exact value1_7.trans (congrArg some (by kernel_rfl))
  · exact value1_8.trans (congrArg some (by kernel_rfl))
theorem value1_steps {im : Image} {b : Nat} (hb : b=45270 ∨ b=45404 ∨ b=45547 ∨ b=45681 ∨ b=45824 ∨ b=45958 ∨ b=46101 ∨ b=46235 ∨ b=46380)
    (hc : CodeAt im (pcOf b) value1Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+624))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+632))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      t.getMem (BitVec.ofNat 64 (region+736))=s.getMem (BitVec.ofNat 64 (source+16)) ∧
      t.getMem (BitVec.ofNat 64 (region+744))=s.getMem (BitVec.ofNat 64 (source+24)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+624 ∨ A=region+632 ∨ A=region+736 ∨ A=region+744) := by
  have ho : Oblig.all s value1_0.res.st.obl := by
    simp only [value1_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value1_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value1_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value1_steps
def value2Code : List (BitVec 32) := bv_list% 32 [0x208b303,0x288b383,0x22643823,0x22743c23,0x2e643823,0x2e743c23]
sym_block value2_0 := symRun { noAlias := true } value2Code (pcOf 45276) 20
sym_block value2_1 := symRun { noAlias := true } value2Code (pcOf 45410) 20
sym_block value2_2 := symRun { noAlias := true } value2Code (pcOf 45553) 20
sym_block value2_3 := symRun { noAlias := true } value2Code (pcOf 45687) 20
sym_block value2_4 := symRun { noAlias := true } value2Code (pcOf 45830) 20
sym_block value2_5 := symRun { noAlias := true } value2Code (pcOf 45964) 20
sym_block value2_6 := symRun { noAlias := true } value2Code (pcOf 46107) 20
sym_block value2_7 := symRun { noAlias := true } value2Code (pcOf 46241) 20
sym_block value2_8 := symRun { noAlias := true } value2Code (pcOf 46386) 20
theorem value2_run {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386) :
    symRun { noAlias := true } value2Code (pcOf b) 20 =
      some ⟨value2_0.res.st,.c (pcOf (b+6)),value2_0.res.stop,value2_0.res.steps,value2_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value2_0.trans (congrArg some (by kernel_rfl))
  · exact value2_1.trans (congrArg some (by kernel_rfl))
  · exact value2_2.trans (congrArg some (by kernel_rfl))
  · exact value2_3.trans (congrArg some (by kernel_rfl))
  · exact value2_4.trans (congrArg some (by kernel_rfl))
  · exact value2_5.trans (congrArg some (by kernel_rfl))
  · exact value2_6.trans (congrArg some (by kernel_rfl))
  · exact value2_7.trans (congrArg some (by kernel_rfl))
  · exact value2_8.trans (congrArg some (by kernel_rfl))
theorem value2_steps {im : Image} {b : Nat} (hb : b=45276 ∨ b=45410 ∨ b=45553 ∨ b=45687 ∨ b=45830 ∨ b=45964 ∨ b=46107 ∨ b=46241 ∨ b=46386)
    (hc : CodeAt im (pcOf b) value2Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+560))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+568))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      t.getMem (BitVec.ofNat 64 (region+752))=s.getMem (BitVec.ofNat 64 (source+32)) ∧
      t.getMem (BitVec.ofNat 64 (region+760))=s.getMem (BitVec.ofNat 64 (source+40)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+560 ∨ A=region+568 ∨ A=region+752 ∨ A=region+760) := by
  have ho : Oblig.all s value2_0.res.st.obl := by
    simp only [value2_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value2_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value2_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value2_steps
def value3Code : List (BitVec 32) := bv_list% 32 [0x308b303,0x388b383,0x1e643823,0x1e743c23,0x30643023,0x30743423]
sym_block value3_0 := symRun { noAlias := true } value3Code (pcOf 45282) 20
sym_block value3_1 := symRun { noAlias := true } value3Code (pcOf 45416) 20
sym_block value3_2 := symRun { noAlias := true } value3Code (pcOf 45559) 20
sym_block value3_3 := symRun { noAlias := true } value3Code (pcOf 45693) 20
sym_block value3_4 := symRun { noAlias := true } value3Code (pcOf 45836) 20
sym_block value3_5 := symRun { noAlias := true } value3Code (pcOf 45970) 20
sym_block value3_6 := symRun { noAlias := true } value3Code (pcOf 46113) 20
sym_block value3_7 := symRun { noAlias := true } value3Code (pcOf 46247) 20
sym_block value3_8 := symRun { noAlias := true } value3Code (pcOf 46392) 20
theorem value3_run {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392) :
    symRun { noAlias := true } value3Code (pcOf b) 20 =
      some ⟨value3_0.res.st,.c (pcOf (b+6)),value3_0.res.stop,value3_0.res.steps,value3_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value3_0.trans (congrArg some (by kernel_rfl))
  · exact value3_1.trans (congrArg some (by kernel_rfl))
  · exact value3_2.trans (congrArg some (by kernel_rfl))
  · exact value3_3.trans (congrArg some (by kernel_rfl))
  · exact value3_4.trans (congrArg some (by kernel_rfl))
  · exact value3_5.trans (congrArg some (by kernel_rfl))
  · exact value3_6.trans (congrArg some (by kernel_rfl))
  · exact value3_7.trans (congrArg some (by kernel_rfl))
  · exact value3_8.trans (congrArg some (by kernel_rfl))
theorem value3_steps {im : Image} {b : Nat} (hb : b=45282 ∨ b=45416 ∨ b=45559 ∨ b=45693 ∨ b=45836 ∨ b=45970 ∨ b=46113 ∨ b=46247 ∨ b=46392)
    (hc : CodeAt im (pcOf b) value3Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+496))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+504))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      t.getMem (BitVec.ofNat 64 (region+768))=s.getMem (BitVec.ofNat 64 (source+48)) ∧
      t.getMem (BitVec.ofNat 64 (region+776))=s.getMem (BitVec.ofNat 64 (source+56)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+496 ∨ A=region+504 ∨ A=region+768 ∨ A=region+776) := by
  have ho : Oblig.all s value3_0.res.st.obl := by
    simp only [value3_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value3_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value3_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value3_steps
def value4Code : List (BitVec 32) := bv_list% 32 [0x408b303,0x488b383,0x1a643823,0x1a743c23,0x30643823,0x30743c23]
sym_block value4_0 := symRun { noAlias := true } value4Code (pcOf 45288) 20
sym_block value4_1 := symRun { noAlias := true } value4Code (pcOf 45422) 20
sym_block value4_2 := symRun { noAlias := true } value4Code (pcOf 45565) 20
sym_block value4_3 := symRun { noAlias := true } value4Code (pcOf 45699) 20
sym_block value4_4 := symRun { noAlias := true } value4Code (pcOf 45842) 20
sym_block value4_5 := symRun { noAlias := true } value4Code (pcOf 45976) 20
sym_block value4_6 := symRun { noAlias := true } value4Code (pcOf 46119) 20
sym_block value4_7 := symRun { noAlias := true } value4Code (pcOf 46253) 20
sym_block value4_8 := symRun { noAlias := true } value4Code (pcOf 46398) 20
theorem value4_run {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398) :
    symRun { noAlias := true } value4Code (pcOf b) 20 =
      some ⟨value4_0.res.st,.c (pcOf (b+6)),value4_0.res.stop,value4_0.res.steps,value4_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value4_0.trans (congrArg some (by kernel_rfl))
  · exact value4_1.trans (congrArg some (by kernel_rfl))
  · exact value4_2.trans (congrArg some (by kernel_rfl))
  · exact value4_3.trans (congrArg some (by kernel_rfl))
  · exact value4_4.trans (congrArg some (by kernel_rfl))
  · exact value4_5.trans (congrArg some (by kernel_rfl))
  · exact value4_6.trans (congrArg some (by kernel_rfl))
  · exact value4_7.trans (congrArg some (by kernel_rfl))
  · exact value4_8.trans (congrArg some (by kernel_rfl))
theorem value4_steps {im : Image} {b : Nat} (hb : b=45288 ∨ b=45422 ∨ b=45565 ∨ b=45699 ∨ b=45842 ∨ b=45976 ∨ b=46119 ∨ b=46253 ∨ b=46398)
    (hc : CodeAt im (pcOf b) value4Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+432))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+440))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      t.getMem (BitVec.ofNat 64 (region+784))=s.getMem (BitVec.ofNat 64 (source+64)) ∧
      t.getMem (BitVec.ofNat 64 (region+792))=s.getMem (BitVec.ofNat 64 (source+72)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+432 ∨ A=region+440 ∨ A=region+784 ∨ A=region+792) := by
  have ho : Oblig.all s value4_0.res.st.obl := by
    simp only [value4_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value4_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value4_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value4_steps
def value5Code : List (BitVec 32) := bv_list% 32 [0x508b303,0x588b383,0x16643823,0x16743c23,0x32643023,0x32743423]
sym_block value5_0 := symRun { noAlias := true } value5Code (pcOf 45294) 20
sym_block value5_1 := symRun { noAlias := true } value5Code (pcOf 45428) 20
sym_block value5_2 := symRun { noAlias := true } value5Code (pcOf 45571) 20
sym_block value5_3 := symRun { noAlias := true } value5Code (pcOf 45705) 20
sym_block value5_4 := symRun { noAlias := true } value5Code (pcOf 45848) 20
sym_block value5_5 := symRun { noAlias := true } value5Code (pcOf 45982) 20
sym_block value5_6 := symRun { noAlias := true } value5Code (pcOf 46125) 20
sym_block value5_7 := symRun { noAlias := true } value5Code (pcOf 46259) 20
sym_block value5_8 := symRun { noAlias := true } value5Code (pcOf 46404) 20
theorem value5_run {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404) :
    symRun { noAlias := true } value5Code (pcOf b) 20 =
      some ⟨value5_0.res.st,.c (pcOf (b+6)),value5_0.res.stop,value5_0.res.steps,value5_0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact value5_0.trans (congrArg some (by kernel_rfl))
  · exact value5_1.trans (congrArg some (by kernel_rfl))
  · exact value5_2.trans (congrArg some (by kernel_rfl))
  · exact value5_3.trans (congrArg some (by kernel_rfl))
  · exact value5_4.trans (congrArg some (by kernel_rfl))
  · exact value5_5.trans (congrArg some (by kernel_rfl))
  · exact value5_6.trans (congrArg some (by kernel_rfl))
  · exact value5_7.trans (congrArg some (by kernel_rfl))
  · exact value5_8.trans (congrArg some (by kernel_rfl))
theorem value5_steps {im : Image} {b : Nat} (hb : b=45294 ∨ b=45428 ∨ b=45571 ∨ b=45705 ∨ b=45848 ∨ b=45982 ∨ b=46125 ∨ b=46259 ∨ b=46404)
    (hc : CodeAt im (pcOf b) value5Code) (s : MachineState) (hp : s.pc=pcOf b)
    (region source : Nat) (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getMem (BitVec.ofNat 64 (region+368))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+376))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      t.getMem (BitVec.ofNat 64 (region+800))=s.getMem (BitVec.ofNat 64 (source+80)) ∧
      t.getMem (BitVec.ofNat 64 (region+808))=s.getMem (BitVec.ofNat 64 (source+88)) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (fun A => A=region+368 ∨ A=region+376 ∨ A=region+800 ∨ A=region+808) := by
  have ho : Oblig.all s value5_0.res.st.obl := by
    simp only [value5_0.res]
    t3n [h8,h17]
    omega
  refine ⟨_,symRun_sound (value5_run hb) hc s hp ho,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,value5_0.res]
    t3n [h8,h17] <;>
      simp (disch := omega) [ofNat_add_ofNat,ofNat_eq_iff,Nat.mod_eq_of_lt] <;>
      (try split_ifs) <;> (first | rfl | omega)
#print axioms value5_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

theorem rotate_raw (raw : Nat) (hr : raw<128) :
    (BitVec.ofNat 64 raw >>> 1) + ((BitVec.ofNat 64 raw &&& 1#64) <<< 6) =
      BitVec.ofNat 64 (raw/2+64*(raw%2)) := by
  have hm : BitVec.ofNat 64 raw &&& 1#64=BitVec.ofNat 64 (raw%2) := by
    simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask raw 1 (by decide)
  rw [ofNat_shr raw 1 (by omega),hm,ofNat_shl,ofNat_add_ofNat]
  congr 1
  simp only [pow_one]
  omega
def entry0Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x85813,0x7f87813,0x2437,0x17040413,0x78b7,0x1088893]
sym_block entry0 := symRun { noAlias := true } entry0Code (pcOf 45257) 32
theorem entry0_steps {im : Image} (hc : CodeAt im (pcOf 45257) entry0Code)
    (s : MachineState) (hp : s.pc=pcOf 45257) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45266 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 8560 ∧
      t.getReg .x17=BitVec.ofNat 64 28688 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry0 hc s hp (by simp [entry0.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry0.res,E.eval]
  · simp only [Result.toState_getReg,entry0.res]
    t3n []
    simpa using hraw
  · simp [entry0.res,rv_simp]
  · simp [entry0.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry0.res,rv_simp]
#print axioms entry0_steps
def entry1Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x8b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x2437,0xdf040413,0x78b7,0xe088893]
sym_block entry1 := symRun { noAlias := true } entry1Code (pcOf 45387) 32
theorem entry1_steps {im : Image} (hc : CodeAt im (pcOf 45387) entry1Code)
    (s : MachineState) (hp : s.pc=pcOf 45387) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131424) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45400 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 7664 ∧
      t.getReg .x17=BitVec.ofNat 64 28896 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry1 hc s hp (by simp [entry1.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry1.res,E.eval]
  · simp only [Result.toState_getReg,entry1.res]
    t3n []
    have hraw' : s.getMem 131424#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry1.res,rv_simp]
  · simp [entry1.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry1.res,rv_simp]
#print axioms entry1_steps
def entry2Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x85813,0x7f87813,0x2437,0xa7040413,0x78b7,0x1b088893]
sym_block entry2 := symRun { noAlias := true } entry2Code (pcOf 45534) 32
theorem entry2_steps {im : Image} (hc : CodeAt im (pcOf 45534) entry2Code)
    (s : MachineState) (hp : s.pc=pcOf 45534) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45543 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 6768 ∧
      t.getReg .x17=BitVec.ofNat 64 29104 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry2 hc s hp (by simp [entry2.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry2.res,E.eval]
  · simp only [Result.toState_getReg,entry2.res]
    t3n []
    simpa using hraw
  · simp [entry2.res,rv_simp]
  · simp [entry2.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry2.res,rv_simp]
#print axioms entry2_steps
def entry3Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x88b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0x6f040413,0x78b7,0x28088893]
sym_block entry3 := symRun { noAlias := true } entry3Code (pcOf 45664) 32
theorem entry3_steps {im : Image} (hc : CodeAt im (pcOf 45664) entry3Code)
    (s : MachineState) (hp : s.pc=pcOf 45664) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131432) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45677 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 5872 ∧
      t.getReg .x17=BitVec.ofNat 64 29312 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry3 hc s hp (by simp [entry3.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry3.res,E.eval]
  · simp only [Result.toState_getReg,entry3.res]
    t3n []
    have hraw' : s.getMem 131432#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry3.res,rv_simp]
  · simp [entry3.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry3.res,rv_simp]
#print axioms entry3_steps
def entry4Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x85813,0x7f87813,0x1437,0x37040413,0x78b7,0x35088893]
sym_block entry4 := symRun { noAlias := true } entry4Code (pcOf 45811) 32
theorem entry4_steps {im : Image} (hc : CodeAt im (pcOf 45811) entry4Code)
    (s : MachineState) (hp : s.pc=pcOf 45811) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 45820 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 4976 ∧
      t.getReg .x17=BitVec.ofNat 64 29520 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry4 hc s hp (by simp [entry4.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry4.res,E.eval]
  · simp only [Result.toState_getReg,entry4.res]
    t3n []
    simpa using hraw
  · simp [entry4.res,rv_simp]
  · simp [entry4.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry4.res,rv_simp]
#print axioms entry4_steps
def entry5Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x108b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0xff040413,0x78b7,0x42088893]
sym_block entry5 := symRun { noAlias := true } entry5Code (pcOf 45941) 32
theorem entry5_steps {im : Image} (hc : CodeAt im (pcOf 45941) entry5Code)
    (s : MachineState) (hp : s.pc=pcOf 45941) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131440) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 45954 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 4080 ∧
      t.getReg .x17=BitVec.ofNat 64 29728 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry5 hc s hp (by simp [entry5.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry5.res,E.eval]
  · simp only [Result.toState_getReg,entry5.res]
    t3n []
    have hraw' : s.getMem 131440#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry5.res,rv_simp]
  · simp [entry5.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry5.res,rv_simp]
#print axioms entry5_steps
def entry6Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x85813,0x7f87813,0x1437,0xc7040413,0x78b7,0x4f088893]
sym_block entry6 := symRun { noAlias := true } entry6Code (pcOf 46088) 32
theorem entry6_steps {im : Image} (hc : CodeAt im (pcOf 46088) entry6Code)
    (s : MachineState) (hp : s.pc=pcOf 46088) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 0 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 9 9 t ∧ t.pc=pcOf 46097 ∧
      t.getReg .x16=BitVec.ofNat 64 raw ∧
      t.getReg .x8=BitVec.ofNat 64 3184 ∧
      t.getReg .x17=BitVec.ofNat 64 29936 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry6 hc s hp (by simp [entry6.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry6.res,E.eval]
  · simp only [Result.toState_getReg,entry6.res]
    t3n []
    simpa using hraw
  · simp [entry6.res,rv_simp]
  · simp [entry6.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry6.res,rv_simp]
#print axioms entry6_steps
def entry7Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x685813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x1437,0x8f040413,0x78b7,0x5c088893]
sym_block entry7 := symRun { noAlias := true } entry7Code (pcOf 46218) 32
theorem entry7_steps {im : Image} (hc : CodeAt im (pcOf 46218) entry7Code)
    (s : MachineState) (hp : s.pc=pcOf 46218) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 6 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 13 13 t ∧ t.pc=pcOf 46231 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 2288 ∧
      t.getReg .x17=BitVec.ofNat 64 30144 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry7 hc s hp (by simp [entry7.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry7.res,E.eval]
  · simp only [Result.toState_getReg,entry7.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 6 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry7.res,rv_simp]
  · simp [entry7.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry7.res,rv_simp]
#print axioms entry7_steps
def entry8Code : List (BitVec 32) := bv_list% 32 [0x208b7,0x16088893,0x188b803,0x2585813,0x7f87813,0x187313,0x631313,0x185813,0x680833,0x57000413,0x78b7,0x69088893]
sym_block entry8 := symRun { noAlias := true } entry8Code (pcOf 46364) 32
theorem entry8_steps {im : Image} (hc : CodeAt im (pcOf 46364) entry8Code)
    (s : MachineState) (hp : s.pc=pcOf 46364) (raw : Nat) (hr : raw<128)
    (hraw : s.getMem (BitVec.ofNat 64 131448) >>> 37 &&& 127#64=BitVec.ofNat 64 raw) :
    ∃ t, Steps im s 12 12 t ∧ t.pc=pcOf 46376 ∧
      t.getReg .x16=BitVec.ofNat 64 (raw/2+64*(raw%2)) ∧
      t.getReg .x8=BitVec.ofNat 64 1392 ∧
      t.getReg .x17=BitVec.ofNat 64 30352 ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound entry8 hc s hp (by simp [entry8.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · simp [entry8.res,E.eval]
  · simp only [Result.toState_getReg,entry8.res]
    t3n []
    have hraw' : s.getMem 131448#64 >>> 37 &&& 127#64=BitVec.ofNat 64 raw := hraw
    rw [hraw']
    exact rotate_raw raw hr
  · simp [entry8.res,rv_simp]
  · simp [entry8.res,rv_simp]
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [entry8.res,rv_simp]
#print axioms entry8_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def planCode : List (BitVec 32) := bv_list% 32 [0x1f87913,0x291313,0x690933,0xff9337,0xf9030313,0x690933]
sym_block plan0 := symRun { noAlias := true } planCode (pcOf 45300) 20
sym_block plan1 := symRun { noAlias := true } planCode (pcOf 45434) 20
sym_block plan2 := symRun { noAlias := true } planCode (pcOf 45577) 20
sym_block plan3 := symRun { noAlias := true } planCode (pcOf 45711) 20
sym_block plan4 := symRun { noAlias := true } planCode (pcOf 45854) 20
sym_block plan5 := symRun { noAlias := true } planCode (pcOf 45988) 20
sym_block plan6 := symRun { noAlias := true } planCode (pcOf 46131) 20
sym_block plan7 := symRun { noAlias := true } planCode (pcOf 46265) 20
sym_block plan8 := symRun { noAlias := true } planCode (pcOf 46410) 20
theorem plan_run {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410) :
    symRun { noAlias := true } planCode (pcOf b) 20 = some
      ⟨plan0.res.st,.c (pcOf (b+6)),plan0.res.stop,plan0.res.steps,plan0.res.cycles⟩ := by
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact plan0.trans (congrArg some (by kernel_rfl))
  · exact plan1.trans (congrArg some (by kernel_rfl))
  · exact plan2.trans (congrArg some (by kernel_rfl))
  · exact plan3.trans (congrArg some (by kernel_rfl))
  · exact plan4.trans (congrArg some (by kernel_rfl))
  · exact plan5.trans (congrArg some (by kernel_rfl))
  · exact plan6.trans (congrArg some (by kernel_rfl))
  · exact plan7.trans (congrArg some (by kernel_rfl))
  · exact plan8.trans (congrArg some (by kernel_rfl))
theorem plan_steps {im : Image} {b : Nat} (hb : b=45300 ∨ b=45434 ∨ b=45577 ∨ b=45711 ∨ b=45854 ∨ b=45988 ∨ b=46131 ∨ b=46265 ∨ b=46410)
    (hc : CodeAt im (pcOf b) planCode) (s : MachineState) (hp : s.pc=pcOf b)
    (child : Nat) (hchild : child<128) (h16 : s.getReg .x16=BitVec.ofNat 64 child) :
    ∃ t, Steps im s 6 6 t ∧ t.pc=pcOf (b+6) ∧
      t.getReg .x18=BitVec.ofNat 64 (16748432+5*(child%32)) ∧
      RegsExcept s t [.x6,.x18] ∧ Frame s t (fun _ => False) := by
  refine ⟨_,symRun_sound (plan_run hb) hc s hp (by simp [plan0.res,rv_simp]),?_,?_,?_,?_⟩
  · simp [Result.toState_pc,E.eval]
  · simp only [Result.toState_getReg,plan0.res]
    t3n [h16]
    have hm : BitVec.ofNat 64 child &&& 31#64 = BitVec.ofNat 64 (child%32) := by
      simpa using SigGolfCandidate.T3M.Sign.ofNat_and_mask child 5 (by decide)
    rw [hm,ofNat_shl]
    simp only [ofNat_add_ofNat]
    congr 1
    norm_num
    omega
  · intro r hr; cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn; simp [plan0.res,rv_simp]
#print axioms plan_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure ValuesCode (im : Image) (b : Nat) : Prop where
  value0 : CodeAt im (pcOf (b+0)) value0Code
  value1 : CodeAt im (pcOf (b+4)) value1Code
  value2 : CodeAt im (pcOf (b+10)) value2Code
  value3 : CodeAt im (pcOf (b+16)) value3Code
  value4 : CodeAt im (pcOf (b+22)) value4Code
  value5 : CodeAt im (pcOf (b+28)) value5Code
def ValuesW (region A : Nat) : Prop :=
  ∃ i<6, A=region+(688-64*i) ∨ A=region+(696-64*i) ∨
    (0 < i ∧ (A=region+720+16*i ∨ A=region+728+16*i))
theorem values_steps {im : Image} {b : Nat} (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376) (hc : ValuesCode im b)
    (s : MachineState) (hp : s.pc=pcOf b) (region source : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t, Steps im s 34 34 t ∧ t.pc=pcOf (b+34) ∧
      (∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(688-64*i)+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      (∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+720+16*i+8*half))=
        s.getMem (BitVec.ofNat 64 (source+16*i+8*half))) ∧
      RegsExcept s t [.x6,.x7] ∧ Frame s t (ValuesW region) := by
  obtain ⟨t0,st0,p0,v0lo,v0hi,r0,f0⟩ := value0_steps (b:=b+0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value0 s (by simpa using hp) region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  have fw0 : Frame s t0 (ValuesW region) := f0.mono (by
    intro A hA h
    refine ⟨0,by decide,?_⟩
    omega)
  have r00 := r0
  have f00 := fw0
  obtain ⟨t1,st1,p1,v1lo,v1hi,l1lo,l1hi,r1,f1⟩ := value1_steps (b:=b+4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value1 t0 (by simpa using p0) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r00.get (by simp),h8]) (by rw [r00.get (by simp),h17])
  have fw1 : Frame t0 t1 (ValuesW region) := f1.mono (by
    intro A hA h
    refine ⟨1,by decide,?_⟩
    omega)
  have r01 : RegsExcept s t1 [.x6,.x7] := (r00.trans r1).mono (by simp)
  have f01 : Frame s t1 (ValuesW region) := (f00.trans fw1).mono (by intro A hA h; exact h.elim id id)
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v1hi
  rw [f00.get (A:=source+16) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1lo
  rw [f00.get (A:=source+24) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l1hi
  obtain ⟨t2,st2,p2,v2lo,v2hi,l2lo,l2hi,r2,f2⟩ := value2_steps (b:=b+10) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value2 t1 (by simpa using p1) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r01.get (by simp),h8]) (by rw [r01.get (by simp),h17])
  have fw2 : Frame t1 t2 (ValuesW region) := f2.mono (by
    intro A hA h
    refine ⟨2,by decide,?_⟩
    omega)
  have r02 : RegsExcept s t2 [.x6,.x7] := (r01.trans r2).mono (by simp)
  have f02 : Frame s t2 (ValuesW region) := (f01.trans fw2).mono (by intro A hA h; exact h.elim id id)
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v2hi
  rw [f01.get (A:=source+32) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2lo
  rw [f01.get (A:=source+40) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l2hi
  obtain ⟨t3,st3,p3,v3lo,v3hi,l3lo,l3hi,r3,f3⟩ := value3_steps (b:=b+16) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value3 t2 (by simpa using p2) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r02.get (by simp),h8]) (by rw [r02.get (by simp),h17])
  have fw3 : Frame t2 t3 (ValuesW region) := f3.mono (by
    intro A hA h
    refine ⟨3,by decide,?_⟩
    omega)
  have r03 : RegsExcept s t3 [.x6,.x7] := (r02.trans r3).mono (by simp)
  have f03 : Frame s t3 (ValuesW region) := (f02.trans fw3).mono (by intro A hA h; exact h.elim id id)
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v3hi
  rw [f02.get (A:=source+48) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3lo
  rw [f02.get (A:=source+56) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l3hi
  obtain ⟨t4,st4,p4,v4lo,v4hi,l4lo,l4hi,r4,f4⟩ := value4_steps (b:=b+22) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value4 t3 (by simpa using p3) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r03.get (by simp),h8]) (by rw [r03.get (by simp),h17])
  have fw4 : Frame t3 t4 (ValuesW region) := f4.mono (by
    intro A hA h
    refine ⟨4,by decide,?_⟩
    omega)
  have r04 : RegsExcept s t4 [.x6,.x7] := (r03.trans r4).mono (by simp)
  have f04 : Frame s t4 (ValuesW region) := (f03.trans fw4).mono (by intro A hA h; exact h.elim id id)
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v4hi
  rw [f03.get (A:=source+64) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4lo
  rw [f03.get (A:=source+72) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l4hi
  obtain ⟨t5,st5,p5,v5lo,v5hi,l5lo,l5hi,r5,f5⟩ := value5_steps (b:=b+28) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hc.value5 t4 (by simpa using p4) region source hr0 hr1 hra hs0 hs1 hsa (by rw [r04.get (by simp),h8]) (by rw [r04.get (by simp),h17])
  have fw5 : Frame t4 t5 (ValuesW region) := f5.mono (by
    intro A hA h
    refine ⟨5,by decide,?_⟩
    omega)
  have r05 : RegsExcept s t5 [.x6,.x7] := (r04.trans r5).mono (by simp)
  have f05 : Frame s t5 (ValuesW region) := (f04.trans fw5).mono (by intro A hA h; exact h.elim id id)
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at v5hi
  rw [f04.get (A:=source+80) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5lo
  rw [f04.get (A:=source+88) (by omega) (by intro h; obtain ⟨j,hj,h⟩:=h; omega)] at l5hi
  have tail4 : Frame t4 t5 (ValuesW region) := fw5
  have exactTail4 := f5
  have tail3 : Frame t3 t5 (ValuesW region) := (fw4.trans tail4).mono (by intro A hA h; exact h.elim id id)
  have exactTail3 := (f4.trans f5)
  have tail2 : Frame t2 t5 (ValuesW region) := (fw3.trans tail3).mono (by intro A hA h; exact h.elim id id)
  have exactTail2 := ((f3.trans f4).trans f5)
  have tail1 : Frame t1 t5 (ValuesW region) := (fw2.trans tail2).mono (by intro A hA h; exact h.elim id id)
  have exactTail1 := (((f2.trans f3).trans f4).trans f5)
  have tail0 : Frame t0 t5 (ValuesW region) := (fw1.trans tail1).mono (by intro A hA h; exact h.elim id id)
  have exactTail0 := ((((f1.trans f2).trans f3).trans f4).trans f5)
  refine ⟨t5,(((((st0.trans st1).trans st2).trans st3).trans st4).trans st5),by simpa using p5,?_,?_,r05,f05⟩
  · intro i hi half hh
    interval_cases i <;> interval_cases half
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0lo
    · rw [exactTail0.get (by omega) (by omega)]
      simpa using v0hi
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using v1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using v2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using v3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using v4hi
    · simpa using v5lo
    · simpa using v5hi
  · intro i hi hz half hh
    have hp : 1 ≤ i := by omega
    interval_cases i <;> interval_cases half
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1lo
    · rw [exactTail1.get (by omega) (by omega)]
      simpa using l1hi
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2lo
    · rw [exactTail2.get (by omega) (by omega)]
      simpa using l2hi
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3lo
    · rw [exactTail3.get (by omega) (by omega)]
      simpa using l3hi
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4lo
    · rw [exactTail4.get (by omega) (by omega)]
      simpa using l4hi
    · simpa using l5lo
    · simpa using l5hi
#print axioms values_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
def PathsW (dst : Nat → Nat) (n A : Nat) : Prop := ∃ i < n, A=dst i ∨ A=dst i+8
structure PathsInv (s : MachineState) (b source : Nat) (dst : Nat → Nat) (n : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+14*n)
  regs : RegsExcept s t [.x6,.x7,.x28]
  frame : Frame s t (PathsW dst n)
  reads : ∀ i<n,∀ half<2,t.getMem (BitVec.ofNat 64 (dst i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
theorem paths_join {im : Image} (s : MachineState) (b source : Nat) (dst : Nat → Nat)
    (hp : s.pc=pcOf b) (hd : ∀ j<5,dst j+16<2^64)
    (hdis : ∀ i<5,∀ j<5,i≠j → dst i+16≤dst j ∨ dst j+16≤dst i)
    (hstep : ∀ j<5,∀ u,PathsInv s b source dst j u →
      ∃ t,Steps im u 14 17 t ∧ t.pc=pcOf (b+14*(j+1)) ∧
        (∀ half<2,t.getMem (BitVec.ofNat 64 (dst j+8*half))=
          s.getMem (BitVec.ofNat 64 (source+96+16*j+8*half))) ∧
        RegsExcept u t [.x6,.x7,.x28] ∧ Frame u t (fun A=>A=dst j ∨ A=dst j+8)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source dst 5 t := by
  have run : ∀ n,n≤5 → ∃ t,Steps im s (14*n) (17*n) t ∧ PathsInv s b source dst n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨s,Steps.refl _,?_,RegsExcept.refl _ _,Frame.refl _ _,?_⟩
      · simpa using hp
      · intro i hi; omega
    | succ n ih =>
      intro hn
      obtain ⟨u,su,hu⟩:=ih (by omega)
      obtain ⟨t,st,tp,tr,rr,ff⟩:=hstep n (by omega) u hu
      refine ⟨t,(su.trans st).of_eq (by omega) (by omega),tp,?_,?_,?_⟩
      · exact (hu.regs.trans rr).mono (by simp)
      · exact (hu.frame.trans ff).mono (by
          intro A hA h
          rcases h with h | h
          · obtain ⟨i,hi,h⟩:=h;exact ⟨i,by omega,h⟩
          · exact ⟨n,by omega,h⟩)
      · intro i hi half hh
        by_cases he:i=n
        · subst i;exact tr half hh
        · have hin:i<n:=by omega
          have hsep:=hdis i (by omega) n (by omega) he
          have hbound:=hd i (by omega)
          rw [ff.get (by omega) (by omega)]
          exact hu.reads i hin half hh
  exact run 5 (by omega)
#print axioms paths_join
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem path_cell0 {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hlc : CodeAt im (pcOf b) [609795]) (hpc : CodeAt im (pcOf (b+1)) pathCode0)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+0))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1))) =
        s.getMem (BitVec.ofNat 64 (source+96)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/1)+8)) =
        s.getMem (BitVec.ofNat 64 (source+104)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/1) ∨ A=destination region slot (child/1)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨0,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path0_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell0
theorem path_cell1 {im : Image} {b : Nat} (hb : b=45320 ∨ b=45454 ∨ b=45597 ∨ b=45731 ∨ b=45874 ∨ b=46008 ∨ b=46151 ∨ b=46285 ∨ b=46430)
    (hlc : CodeAt im (pcOf b) [1658371]) (hpc : CodeAt im (pcOf (b+1)) pathCode1)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+1))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2))) =
        s.getMem (BitVec.ofNat 64 (source+112)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2)+8)) =
        s.getMem (BitVec.ofNat 64 (source+120)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/2) ∨ A=destination region slot (child/2)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨1,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path1_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell1
theorem path_cell2 {im : Image} {b : Nat} (hb : b=45334 ∨ b=45468 ∨ b=45611 ∨ b=45745 ∨ b=45888 ∨ b=46022 ∨ b=46165 ∨ b=46299 ∨ b=46444)
    (hlc : CodeAt im (pcOf b) [2706947]) (hpc : CodeAt im (pcOf (b+1)) pathCode2)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+2))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4))) =
        s.getMem (BitVec.ofNat 64 (source+128)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/4)+8)) =
        s.getMem (BitVec.ofNat 64 (source+136)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/4) ∨ A=destination region slot (child/4)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨2,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path2_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell2
theorem path_cell3 {im : Image} {b : Nat} (hb : b=45348 ∨ b=45482 ∨ b=45625 ∨ b=45759 ∨ b=45902 ∨ b=46036 ∨ b=46179 ∨ b=46313 ∨ b=46458)
    (hlc : CodeAt im (pcOf b) [3755523]) (hpc : CodeAt im (pcOf (b+1)) pathCode3)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+3))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8))) =
        s.getMem (BitVec.ofNat 64 (source+144)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/8)+8)) =
        s.getMem (BitVec.ofNat 64 (source+152)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/8) ∨ A=destination region slot (child/8)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨3,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path3_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell3
theorem path_cell4 {im : Image} {b : Nat} (hb : b=45362 ∨ b=45496 ∨ b=45639 ∨ b=45773 ∨ b=45916 ∨ b=46050 ∨ b=46193 ∨ b=46327 ∨ b=46472)
    (hlc : CodeAt im (pcOf b) [4804099]) (hpc : CodeAt im (pcOf (b+1)) pathCode4)
    (s : MachineState) (hp : s.pc=pcOf b) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+4))=BitVec.ofNat 8 slot) :
    ∃ t, Steps im s 14 17 t ∧ t.pc=pcOf (b+14) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16))) =
        s.getMem (BitVec.ofNat 64 (source+160)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/16)+8)) =
        s.getMem (BitVec.ofNat 64 (source+168)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A => A=destination region slot (child/16) ∨ A=destination region slot (child/16)+8) := by
  obtain ⟨u,su,upc,u28,ur,uf⟩ := load_plan_step (pcOf b) hlc ⟨4,by decide⟩ (by kernel_rfl)
    s hp table slot ht hbnd h18 hbyte
  have upc' : u.pc=pcOf (b+1) := by rw [upc]; simp [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]
  obtain ⟨t,st,tpc,tlo,thi,tr,tf⟩ := path4_steps_rebased (b:=b+1)
    (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp) hpc u upc'
    region source child slot hr0 hr1 hra hs0 hs1 hsa hj hbnd
    (by rw [ur.get (by decide),h8]) (by rw [ur.get (by decide),h16])
    (by rw [ur.get (by decide),h17]) u28
  refine ⟨t,su.trans st,by simpa [Nat.add_assoc] using tpc,?_,?_,?_,?_⟩
  · rw [uf.get (by omega) (fun h => h)] at tlo
    simpa using tlo
  · rw [uf.get (by omega) (fun h => h)] at thi
    simpa using thi
  · exact (ur.trans tr).mono (by simp)
  · exact (uf.trans tf).mono (fun A _ h => by simpa using h)
#print axioms path_cell4
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The copied siblings occupy separate aligned digest slots and leave both carried pads intact. -/
def ScatterSafe (child : Nat) : Prop :=
  (∀ l : Fin 5, block child l.val % 16 = 0 ∧ block child l.val / 16 < 53 ∧
    sibling child l.val + 16 ≤ 320 ∧ sibling child l.val ≠ 144) ∧
  (∀ i l : Fin 5, i ≠ l → sibling child i.val + 16 ≤ sibling child l.val ∨
    sibling child l.val + 16 ≤ sibling child i.val)
theorem scatterSafe : ∀ child : Fin 128, ScatterSafe child.val := by
  intro child
  fin_cases child <;> unfold ScatterSafe <;> decide +kernel

theorem slots_bound (child : Fin 128) (l : Fin 5) : block child.val l.val / 16 < 53 :=
  ((scatterSafe child).1 l).2.1

theorem block_reassemble (child : Fin 128) (l : Fin 5) :
    16 * (block child.val l.val / 16) = block child.val l.val := by
  have h:=((scatterSafe child).1 l).1
  omega

#print axioms scatterSafe
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem plan_data : ∀ child : Fin 32, ∀ level : Fin 5,
    SigGolfCandidate.T3M.Images.expandSharedData.getD (1024+5*child.val+level.val) 0 =
      BitVec.ofNat 8 (block child.val level.val / 16) := by
  intro child level
  fin_cases child <;> fin_cases level <;> decide +kernel
#print axioms plan_data
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathWords (j : Fin 5) : List (BitVec 32) :=
  match j.val with | 0=>pathCode0 | 1=>pathCode1 | 2=>pathCode2 | 3=>pathCode3 | _=>pathCode4
structure PathsCode (im : Image) (b : Nat) : Prop where
  load : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val)) [BitVec.ofNat 32 (609795+1048576*j.val)]
  path : ∀ j : Fin 5,CodeAt im (pcOf (b+14*j.val+1)) (pathWords j)
theorem path_cell {im : Image} {b : Nat} (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (j : Fin 5)
    (s : MachineState) (hp : s.pc=pcOf (b+14*j.val)) (region source child table slot : Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hj : child<128) (hbnd : slot<53) (ht : table+5<2^24)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbyte : s.getByte (BitVec.ofNat 64 (table+j.val))=BitVec.ofNat 8 slot) :
    ∃ t,Steps im s 14 17 t ∧ t.pc=pcOf (b+14*(j.val+1)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val)) ∧
      t.getMem (BitVec.ofNat 64 (destination region slot (child/2^j.val)+8))=
        s.getMem (BitVec.ofNat 64 (source+96+16*j.val+8)) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧
      Frame s t (fun A=>A=destination region slot (child/2^j.val) ∨ A=destination region slot (child/2^j.val)+8) := by
  fin_cases j
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell0 (b:=b+14*0) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨0,by decide⟩) (by simpa [pathWords] using hc.path ⟨0,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell1 (b:=b+14*1) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨1,by decide⟩) (by simpa [pathWords] using hc.path ⟨1,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell2 (b:=b+14*2) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨2,by decide⟩) (by simpa [pathWords] using hc.path ⟨2,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell3 (b:=b+14*3) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨3,by decide⟩) (by simpa [pathWords] using hc.path ⟨3,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte
  · simpa [Nat.mul_add,Nat.mul_one,Nat.add_assoc] using
      path_cell4 (b:=b+14*4) (by rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
        (hc.load ⟨4,by decide⟩) (by simpa [pathWords] using hc.path ⟨4,by decide⟩) s hp region source child table slot
        hr0 hr1 hra hs0 hs1 hsa hj hbnd ht h8 h16 h17 h18 hbyte

#print axioms path_cell
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def pathDestination (region child : Nat) (slots : Nat → Nat) (j : Nat) : Nat :=
  destination region (slots j) (child/2^j)
theorem five_paths {im : Image} {b : Nat}
    (hb : b=45306 ∨ b=45440 ∨ b=45583 ∨ b=45717 ∨ b=45860 ∨ b=45994 ∨ b=46137 ∨ b=46271 ∨ b=46416)
    (hc : PathsCode im b) (s : MachineState) (hp : s.pc=pcOf b)
    (region source child table : Nat) (slots : Nat → Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (ht0 : 10000 ≤ table) (ht1 : table+5<2^24)
    (hslots : ∀j<5,slots j<53)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source) (h18 : s.getReg .x18=BitVec.ofNat 64 table)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 70 85 t ∧ PathsInv s b source (pathDestination region child slots) 5 t := by
  have hdst : ∀j<5,pathDestination region child slots j+16 ≤ 9456 := by
    intro j hj
    have hs:=hslots j hj
    unfold pathDestination destination
    omega
  apply paths_join s b source (pathDestination region child slots) hp
    (fun j hj=>by have:=hdst j hj;omega) hdis
  intro j hj u hu
  have ub : u.getByte (BitVec.ofNat 64 (table+j))=BitVec.ofNat 8 (slots j) := by
    rw [hu.frame.getByte (by omega) (by
      rintro ⟨i,hi,h⟩
      have hd:=hdst i (by omega)
      omega)]
    exact hbytes j hj
  obtain ⟨t,st,tp,tlo,thi,tr,tf⟩:=path_cell hb hc ⟨j,hj⟩ u hu.pc region source child table (slots j)
    hr0 hr1 hra hs0 hs1 hsa hchild (hslots j hj) ht1
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17]) (by rw [hu.regs.get (by decide),h18]) ub
  have oldlo : u.getMem (BitVec.ofNat 64 (source+96+16*j))=s.getMem (BitVec.ofNat 64 (source+96+16*j)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  have oldhi : u.getMem (BitVec.ofNat 64 (source+96+16*j+8))=s.getMem (BitVec.ofNat 64 (source+96+16*j+8)) :=
    hu.frame.get (by omega) (by
      rintro ⟨i,hi,h⟩;have hd:=hdst i (by omega);omega)
  rw [oldlo] at tlo
  rw [oldhi] at thi
  refine ⟨t,st,tp,?_,tr,tf⟩
  intro half hh
  interval_cases half
  · simpa [pathDestination] using tlo
  · simpa [pathDestination] using thi
#print axioms five_paths
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
theorem path_slot (region : Nat) (child : Fin 128) (level : Fin 5) :
    destination region (block child.val level.val / 16) (child.val / 2^level.val) =
      region + sibling child.val level.val := by
  unfold destination sibling bitAt
  rw [block_reassemble child level]
  omega

theorem path_slots_disjoint (region : Nat) (child : Fin 128) (i j : Fin 5) (hne : i ≠ j) :
    destination region (block child.val i.val / 16) (child.val / 2^i.val)+16 ≤
      destination region (block child.val j.val / 16) (child.val / 2^j.val) ∨
    destination region (block child.val j.val / 16) (child.val / 2^j.val)+16 ≤
      destination region (block child.val i.val / 16) (child.val / 2^i.val) := by
  rw [path_slot, path_slot]
  have h:=(scatterSafe child).2 i j hne
  omega

theorem path_slot_bound (region : Nat) (child : Fin 128) (level : Fin 5) :
    region ≤ destination region (block child.val level.val / 16) (child.val / 2^level.val) ∧
    destination region (block child.val level.val / 16) (child.val / 2^level.val)+16 ≤ region+320 := by
  rw [path_slot]
  have h:=((scatterSafe child).1 level).2.2.1
  omega

#print axioms path_slot
#print axioms path_slots_disjoint
#print axioms path_slot_bound
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
def entryStart (k : Nat) : Nat := [45257, 45387, 45534, 45664, 45811, 45941, 46088, 46218, 46364].getD k 0
def valueStart (k : Nat) : Nat := [45266, 45400, 45543, 45677, 45820, 45954, 46097, 46231, 46376].getD k 0
def planStart (k : Nat) : Nat := [45300, 45434, 45577, 45711, 45854, 45988, 46131, 46265, 46410].getD k 0
def pathStart (k : Nat) : Nat := [45306, 45440, 45583, 45717, 45860, 45994, 46137, 46271, 46416].getD k 0
def topStart (k : Nat) : Nat := [45376, 45523, 45653, 45800, 45930, 46077, 46207, 46354, 46499].getD k 0
def sixthStart (k : Nat) : Nat := [45510, 45787, 46064, 46341, 46486].getD k 0
def entryWords (k : Nat) : List (BitVec 32) := [entry0Code, entry1Code, entry2Code, entry3Code, entry4Code, entry5Code, entry6Code, entry7Code, entry8Code].getD k []
def topWords (k : Nat) : List (BitVec 32) := [topCode0, topCode1, topCode2, topCode3, topCode4, topCode5, topCode6, topCode7, topCode8].getD k []
theorem valuesCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : ValuesCode im (valueStart k.val) := by
  fin_cases k
  · constructor
    · exact SharedCounterHooks.code_slice (off:=210) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=214) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=220) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=226) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=232) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=238) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=344) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=348) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=354) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=360) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=366) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=372) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=487) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=491) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=497) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=503) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=509) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=515) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=621) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=625) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=631) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=637) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=643) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=649) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=764) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=768) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=774) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=780) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=786) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=792) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=898) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=902) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=908) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=914) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=920) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=926) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1041) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1045) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1051) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1057) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1063) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1069) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1175) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1179) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1185) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1191) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1197) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1203) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · exact SharedCounterHooks.code_slice (off:=1320) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1324) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1330) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1336) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1342) hc (by decide +kernel) (by decide +kernel)
    · exact SharedCounterHooks.code_slice (off:=1348) hc (by decide +kernel) (by decide +kernel)
theorem pathsCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : PathsCode im (pathStart k.val) := by
  fin_cases k
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=250) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=264) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=278) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=292) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=306) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=251) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=265) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=279) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=293) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=307) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=384) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=398) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=412) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=426) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=440) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=385) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=399) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=413) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=427) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=441) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=527) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=541) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=555) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=569) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=583) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=528) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=542) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=556) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=570) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=584) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=661) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=675) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=689) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=703) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=717) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=662) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=676) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=690) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=704) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=718) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=804) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=818) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=832) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=846) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=860) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=805) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=819) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=833) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=847) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=861) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=938) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=952) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=966) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=980) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=994) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=939) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=953) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=967) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=981) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=995) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1081) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1095) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1109) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1123) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1137) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1082) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1096) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1110) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1124) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1138) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1215) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1229) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1243) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1257) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1271) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1216) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1230) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1244) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1258) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1272) hc (by decide +kernel) (by decide +kernel)
  · constructor
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1360) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1374) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1388) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1402) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1416) hc (by decide +kernel) (by decide +kernel)
    · intro j; fin_cases j
      · exact SharedCounterHooks.code_slice (off:=1361) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1375) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1389) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1403) hc (by decide +kernel) (by decide +kernel)
      · exact SharedCounterHooks.code_slice (off:=1417) hc (by decide +kernel) (by decide +kernel)
theorem planCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (planStart k.val)) planCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=244) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=378) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=521) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=655) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=798) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=932) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1075) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1209) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1354) hc (by decide +kernel) (by decide +kernel)
theorem entryCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=201) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=331) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=478) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=608) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=755) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=885) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1032) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1162) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1308) hc (by decide +kernel) (by decide +kernel)
theorem topCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 9) : CodeAt im (pcOf (topStart k.val)) (topWords k.val) := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=320) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=467) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=597) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=744) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=874) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1021) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1151) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1298) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1443) hc (by decide +kernel) (by decide +kernel)
theorem sixthCode_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) (k : Fin 5) : CodeAt im (pcOf (sixthStart k.val)) sixthCode := by
  fin_cases k
  · exact SharedCounterHooks.code_slice (off:=454) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=731) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1008) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1285) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1430) hc (by decide +kernel) (by decide +kernel)
#print axioms valuesCode_of_driver
#print axioms pathsCode_of_driver
#print axioms planCode_of_driver
#print axioms entryCode_of_driver
#print axioms topCode_of_driver
#print axioms sixthCode_of_driver
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing
open SigGolfCandidate.Research.SharedPathPacking
theorem plan_data_for_child (child : Fin 128) (level : Fin 5) :
    SigGolfCandidate.T3M.Images.expandSharedData.getD (1024+5*(child.val%32)+level.val) 0 =
      BitVec.ofNat 8 (block child.val level.val / 16) := by
  have h:=plan_data ⟨child.val%32,Nat.mod_lt _ (by decide)⟩ level
  simpa [block] using h
#print axioms plan_data_for_child
end ClaudeWCT.W9.Machine.Expand.SharedScatter.Packing

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def coordRegion (k : Nat) : Nat := 8560-896*k
def coordSource (k : Nat) : Nat := 28688+208*k
def coordPhysical (k raw : Nat) : Nat := if k<8 ∧ k%2=0 then raw else raw/2+64*(raw%2)
def rawAddress (k : Nat) : Nat := [131424,131424,131432,131432,131440,131440,131448,131448,131448].getD k 0
def rawShift (k : Nat) : Nat := [0,6,0,6,0,6,0,6,37].getD k 0
def entryCycles (k : Nat) : Nat := [9,13,9,13,9,13,9,13,12].getD k 0
theorem coordPhysical_lt (k : Nat) (raw : Fin 128) : coordPhysical k raw.val<128 := by
  unfold coordPhysical
  split_ifs
  · exact raw.isLt
  · have:=Nat.mod_lt raw.val (by decide : 0<2);omega

theorem entry_setup {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val) :
    ∃ t, Steps im s (entryCycles k.val) (entryCycles k.val) t ∧ t.pc=pcOf (valueStart k.val) ∧
      t.getReg .x16=BitVec.ofNat 64 (coordPhysical k.val raw.val) ∧
      t.getReg .x8=BitVec.ofNat 64 (coordRegion k.val) ∧
      t.getReg .x17=BitVec.ofNat 64 (coordSource k.val) ∧
      RegsExcept s t [.x6,.x8,.x16,.x17] ∧ Frame s t (fun _=>False) := by
  fin_cases k
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry0_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry1_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry2_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry3_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry4_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry5_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry6_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry7_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
  · simpa [entryCycles,valueStart,coordPhysical,coordRegion,coordSource] using entry8_steps (by simpa [entryStart,entryWords] using hc) s hp raw.val raw.isLt hraw
#print axioms entry_setup
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def topDest (k child : Nat) : Nat := [topDest0 child,topDest1 child,topDest2 child,topDest3 child,topDest4 child,topDest5 child,topDest6 child,topDest7 child,topDest8 child].getD k 0
def topInput (k : Nat) : Nat := if k<8 ∧ k%2=0 then 176 else 192
def nextEntry (k : Nat) : Nat := [45387,45534,45664,45811,45941,46088,46218,46364,46509].getD k 0
def topSteps (k : Nat) : Nat := if k<7 then 11 else 10
theorem top_copy {im : Image} (k : Fin 9)
    (hc : CodeAt im (pcOf (topStart k.val)) (topWords k.val))
    (s : MachineState) (hp : s.pc=pcOf (topStart k.val)) (source : Nat) (child : Fin 128)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h16 : s.getReg .x16=BitVec.ofNat 64 child.val) (h17 : s.getReg .x17=BitVec.ofNat 64 source) :
    ∃ t,Steps im s (topSteps k.val) (topSteps k.val+3) t ∧ t.pc=pcOf (nextEntry k.val) ∧
      (∀half<2,t.getMem (BitVec.ofNat 64 (topDest k.val child.val+8*half))=
        s.getMem (BitVec.ofNat 64 (source+topInput k.val+8*half))) ∧
      RegsExcept s t [.x6,.x7,.x28] ∧ Frame s t (fun A=>A=topDest k.val child.val ∨ A=topDest k.val child.val+8) := by
  fin_cases k
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top0_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top1_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top2_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top3_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top4_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top5_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top6_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top7_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
  · obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=top8_steps (by simpa [topStart,topWords] using hc) s hp source child.val hs0 hs1 hsa child.isLt h16 h17
    refine ⟨t,st,tp,?_,tr,tf⟩
    intro half hh
    interval_cases half
    · simpa [topDest,topInput] using lo
    · simpa [topDest,topInput] using hi
#print axioms top_copy
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def PayloadW (region child : Nat) (slots : Nat → Nat) (A : Nat) : Prop :=
  ValuesW region A ∨ PathsW (pathDestination region child slots) 5 A
structure PayloadPost (s : MachineState) (b region source child : Nat) (slots : Nat → Nat)
    (t : MachineState) : Prop where
  pc : t.pc=pcOf (b+110)
  values : ∀ i<6,∀ half<2,t.getMem (BitVec.ofNat 64 (region+(688-64*i)+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀ half<2,t.getMem (BitVec.ofNat 64 (region+720+16*i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀ i<5,∀ half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=
    s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (PayloadW region child slots)
theorem payload_steps {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (hchild : child<128) (hslots : ∀j<5,slots j<53)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (hdis : ∀i<5,∀j<5,i ≠ j → pathDestination region child slots i+16 ≤ pathDestination region child slots j ∨
      pathDestination region child slots j+16 ≤ pathDestination region child slots i)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j)) :
    ∃ t,Steps im s 110 125 t ∧ PayloadPost s b region source child slots t := by
  obtain ⟨u,su,up,uv,ue,ur,uf⟩:=values_steps hb hv s hpc region source hr0 hr1 hra hs0 hs1 hsa h8 h17
  obtain ⟨v,uvs,vp,vt,vr,vf⟩:=plan_steps (b:=b+34) (by omega) hp u up child hchild
    (by rw [ur.get (by decide),h16])
  have sf : Frame s v (ValuesW region) := (uf.trans vf).mono (by intro A hA h;exact h.elim id False.elim)
  have sr : RegsExcept s v [.x6,.x7,.x18] := (ur.trans vr).mono (by simp)
  have vb : ∀j<5,v.getByte (BitVec.ofNat 64 (16748432+5*(child%32)+j))=BitVec.ofNat 8 (slots j) := by
    intro j hj
    rw [sf.getByte (by have:=Nat.mod_lt child (by decide : 0<32);omega) (by
      rintro ⟨i,hi,h⟩;omega)]
    exact hbytes j hj
  obtain ⟨t,st,ht⟩:=five_paths (b:=b+40) (by omega) hd v (by simpa [Nat.add_assoc] using vp)
    region source child (16748432+5*(child%32)) slots hr0 hr1 hra hs0 hs1 hsa hchild
    (by omega) (by have:=Nat.mod_lt child (by decide : 0<32);omega) hslots hdis
    (by rw [sr.get (by decide),h8]) (by rw [sr.get (by decide),h16])
    (by rw [sr.get (by decide),h17]) vt vb
  refine ⟨t,((su.trans uvs).trans st).of_eq (by omega) (by omega),?_,?_,?_,?_,?_,?_⟩
  · simpa [Nat.add_assoc] using ht.pc
  · intro i hi half hh
    have ilow : 368 ≤ 688-64*i := by omega
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact uv i hi half hh
  · intro i hi hip half hh
    rw [ht.frame.get (by omega) (by rintro ⟨j,hj,h⟩;have:=hdst j hj;omega)]
    rw [vf.get (by omega) (by simp)]
    exact ue i hi hip half hh
  · intro i hi half hh
    rw [ht.reads i hi half hh]
    exact sf.get (by omega) (by rintro ⟨j,hj,h⟩;omega)
  · exact (sr.trans ht.regs).mono (by simp)
  · exact (sf.trans ht.frame).mono (by intro A hA h;exact h)
#print axioms payload_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M
theorem installed_values (k : Fin 9) : ValuesCode Images.expandImage (valueStart k.val) :=
  valuesCode_of_driver codeAt_expand_shared_driver k
theorem installed_paths (k : Fin 9) : PathsCode Images.expandImage (pathStart k.val) :=
  pathsCode_of_driver codeAt_expand_shared_driver k
theorem installed_plan (k : Fin 9) : CodeAt Images.expandImage (pcOf (planStart k.val)) planCode :=
  planCode_of_driver codeAt_expand_shared_driver k
theorem installed_entry (k : Fin 9) : CodeAt Images.expandImage (pcOf (entryStart k.val)) (entryWords k.val) :=
  entryCode_of_driver codeAt_expand_shared_driver k
theorem installed_top (k : Fin 9) : CodeAt Images.expandImage (pcOf (topStart k.val)) (topWords k.val) :=
  topCode_of_driver codeAt_expand_shared_driver k
theorem installed_sixth (k : Fin 5) : CodeAt Images.expandImage (pcOf (sixthStart k.val)) sixthCode :=
  sixthCode_of_driver codeAt_expand_shared_driver k
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def SixthW (region child A : Nat) : Prop := A=destination region 52 (child/32) ∨ A=destination region 52 (child/32)+8
structure ExtendedPost (s : MachineState) (region source child : Nat) (slots : Nat → Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (region+(688-64*i)+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  ends : ∀ i < 6, 0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (region+720+16*i+8*half))=s.getMem (BitVec.ofNat 64 (source+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination region child slots i+8*half))=s.getMem (BitVec.ofNat 64 (source+96+16*i+8*half))
  sixth : ∀half<2,t.getMem (BitVec.ofNat 64 (destination region 52 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (source+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (fun A=>PayloadW region child slots A ∨ SixthW region child A)
theorem payload_sixth {im : Image} {b : Nat}
    (hb : b+110=45510 ∨ b+110=45787 ∨ b+110=46064 ∨ b+110=46341 ∨ b+110=46486)
    (hc : CodeAt im (pcOf (b+110)) sixthCode) {s u : MachineState}
    (region source child : Nat) (slots : Nat → Nat)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0) (hchild : child<128)
    (hdst : ∀j<5,pathDestination region child slots j+16 ≤ region+320)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hu : PayloadPost s b region source child slots u) :
    ∃t,Steps im u 13 16 t ∧ t.pc=pcOf (b+123) ∧ ExtendedPost s region source child slots t := by
  obtain ⟨t,st,tp,lo,hi,tr,tf⟩:=sixth_steps_rebased hb hc u hu.pc region source child
    hr0 hr1 hra hs0 hs1 hsa hchild
    (by rw [hu.regs.get (by decide),h8]) (by rw [hu.regs.get (by decide),h16])
    (by rw [hu.regs.get (by decide),h17])
  have hd : region+832 ≤ destination region 52 (child/32) ∧ destination region 52 (child/32)+16 ≤ region+896 := by
    unfold destination
    have:=Nat.mod_lt (child/32) (by decide : 0<2)
    omega
  refine ⟨t,st,by simpa [Nat.add_assoc] using tp,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.values i hi half hh
  · intro i hi hip half hh
    rw [tf.get (by omega) (by omega)]
    exact hu.ends i hi hip half hh
  · intro i hi half hh
    have hdi:=hdst i hi
    rw [tf.get (by omega) (by omega)]
    exact hu.paths i hi half hh
  · intro half hh
    have hsfr : ∀off,176 ≤ off → off ≤184 → u.getMem (BitVec.ofNat 64 (source+off))=s.getMem (BitVec.ofNat 64 (source+off)) := by
      intro off hlo hhi
      apply hu.frame.get (by omega)
      rintro (h|h)
      · obtain ⟨j,hj,h⟩:=h;omega
      · obtain ⟨j,hj,h⟩:=h;have:=hdst j hj;omega
    interval_cases half
    · simpa only [Nat.mul_zero,Nat.add_zero,hsfr 176 (by omega) (by omega)] using lo
    · simpa only [Nat.mul_one,show source+176+8=source+184 by omega,hsfr 184 (by omega) (by omega)] using hi
  · exact (hu.regs.trans tr).mono (by simp)
  · exact (hu.frame.trans tf).mono (by intro A hA h;exact h)
#print axioms payload_sixth
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def packedSlots (child j : Nat) : Nat := block child j / 16

theorem payload_packed {im : Image} {b : Nat}
    (hb : b=45266 ∨ b=45400 ∨ b=45543 ∨ b=45677 ∨ b=45820 ∨ b=45954 ∨ b=46097 ∨ b=46231 ∨ b=46376)
    (hv : ValuesCode im b) (hp : CodeAt im (pcOf (b+34)) planCode) (hd : PathsCode im (b+40))
    (s : MachineState) (hpc : s.pc=pcOf b) (region source : Nat) (child : Fin 128)
    (hr0 : 1376 ≤ region) (hr1 : region ≤ 8560) (hra : region%8=0)
    (hs0 : 28672 ≤ source) (hs1 : source ≤ 31000) (hsa : source%8=0)
    (h8 : s.getReg .x8=BitVec.ofNat 64 region) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 source)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s 110 125 t ∧ PayloadPost s b region source child.val (packedSlots child.val) t := by
  apply payload_steps hb hv hp hd s hpc region source child.val (packedSlots child.val)
    hr0 hr1 hra hs0 hs1 hsa child.isLt
    (fun j hj=>Packing.slots_bound child ⟨j,hj⟩) ?_ ?_ h8 h16 h17 hbytes
  · intro j hj
    exact (Packing.path_slot_bound region child ⟨j,hj⟩).2
  · intro i hi j hj hne
    exact Packing.path_slots_disjoint region child ⟨i,hi⟩ ⟨j,hj⟩ (by intro h;exact hne (congrArg Fin.val h))

theorem payload_packed_paths {s t : MachineState} {b region source : Nat} {child : Fin 128}
    (h : PayloadPost s b region source child.val (packedSlots child.val) t) (j : Fin 5) (half : Fin 2) :
    t.getMem (BitVec.ofNat 64 (region+sibling child.val j.val+8*half.val))=
      s.getMem (BitVec.ofNat 64 (source+96+16*j.val+8*half.val)) := by
  have hread:=h.paths j.val j.isLt half.val half.isLt
  simpa only [pathDestination,packedSlots,Packing.path_slot region child j] using hread
#print axioms payload_packed
#print axioms payload_packed_paths
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def firstCoord (k : Nat) : Prop := k<8 ∧ k%2=0
instance (k : Nat) : Decidable (firstCoord k) := inferInstanceAs (Decidable (k<8 ∧ k%2=0))
def bodyInstructions (k : Nat) : Nat := if firstCoord k then 110 else 123
def bodyCycles (k : Nat) : Nat := if firstCoord k then 125 else 141
def LocalW (region child A : Nat) : Prop := PayloadW region child (packedSlots child) A ∨ SixthW region child A
structure BodyPost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (topStart k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(688-64*i)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀ i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+720+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 52 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  regs : RegsExcept s t [.x6,.x7,.x18,.x28]
  frame : Frame s t (LocalW (coordRegion k) child)
theorem body_steps {im : Image} (k : Fin 9)
    (hv : ValuesCode im (valueStart k.val))
    (hp : CodeAt im (pcOf (planStart k.val)) planCode)
    (hd : PathsCode im (pathStart k.val))
    (hx : ¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s : MachineState) (hpc : s.pc=pcOf (valueStart k.val)) (child : Fin 128)
    (h8 : s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16 : s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17 : s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=
      BitVec.ofNat 8 (packedSlots child.val j)) :
    ∃t,Steps im s (bodyInstructions k.val) (bodyCycles k.val) t ∧ BodyPost s k.val child.val t := by
  have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
  have hpl : valueStart k.val+34=planStart k.val := by fin_cases k <;> decide
  have hpa : valueStart k.val+40=pathStart k.val := by fin_cases k <;> decide
  have r0 : 1376 ≤ coordRegion k.val := by fin_cases k <;> decide
  have r1 : coordRegion k.val ≤ 8560 := by fin_cases k <;> decide
  have ra : coordRegion k.val%8=0 := by fin_cases k <;> decide
  have s0 : 28672 ≤ coordSource k.val := by fin_cases k <;> decide
  have s1 : coordSource k.val ≤ 31000 := by fin_cases k <;> decide
  have sa : coordSource k.val%8=0 := by fin_cases k <;> decide
  obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
    s hpc (coordRegion k.val) (coordSource k.val) child r0 r1 ra s0 s1 sa h8 h16 h17 hbytes
  by_cases hf:firstCoord k.val
  · have pc : valueStart k.val+110=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    refine ⟨u,by simpa [bodyInstructions,bodyCycles,hf] using su,?_,hu.values,hu.ends,hu.paths,?_,hu.regs,?_⟩
    · simpa [pc] using hu.pc
    · intro hn;exact (hn hf).elim
    · exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · have h6 : valueStart k.val+110=45510 ∨ valueStart k.val+110=45787 ∨ valueStart k.val+110=46064 ∨ valueStart k.val+110=46341 ∨ valueStart k.val+110=46486 := by
      fin_cases k <;> simp_all [firstCoord,valueStart]
    have pc : valueStart k.val+123=topStart k.val := by fin_cases k <;> simp_all [firstCoord,valueStart,topStart]
    obtain ⟨t,ut,tp,ht⟩:=payload_sixth h6 (hx hf) (coordRegion k.val) (coordSource k.val) child.val (packedSlots child.val)
      r0 r1 ra s0 s1 sa child.isLt (fun j hj=>(Packing.path_slot_bound (coordRegion k.val) child ⟨j,hj⟩).2) h8 h16 h17 hu
    refine ⟨t,?_,?_,ht.values,ht.ends,ht.paths,fun _=>ht.sixth,ht.regs,ht.frame⟩
    · simpa [bodyInstructions,bodyCycles,hf] using su.trans ut
    · simpa [pc] using tp
#print axioms body_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
theorem localW_bounds (region : Nat) (child : Fin 128) (A : Nat)
    (h : LocalW region child.val A) : region ≤ A ∧ A+8 ≤ region+896 := by
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    omega
  · obtain ⟨i,hi,h⟩:=h
    have hb:=Packing.path_slot_bound region child ⟨i,hi⟩
    change region ≤ pathDestination region child.val (packedSlots child.val) i ∧
      pathDestination region child.val (packedSlots child.val) i+16 ≤ region+320 at hb
    omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    omega

theorem topDest_bound (k : Fin 9) (child : Fin 128) : topDest k.val child.val+16 ≤ coordRegion k.val := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_bounds (k : Fin 9) : 1376 ≤ coordRegion k.val ∧ coordRegion k.val ≤ 8560 ∧ coordRegion k.val%8=0 := by
  fin_cases k <;> decide

theorem coordSource_bounds (k : Fin 9) : 28672 ≤ coordSource k.val ∧ coordSource k.val ≤ 31000 ∧ coordSource k.val%8=0 := by
  fin_cases k <;> decide

def coordinateInstructions (k : Nat) : Nat := entryCycles k+bodyInstructions k+topSteps k
def coordinateCycles (k : Nat) : Nat := entryCycles k+bodyCycles k+topSteps k+3

theorem coordinateBounds (k : Fin 9) : coordinateInstructions k.val ≤ 150 ∧ coordinateCycles k.val ≤ 170 := by
  fin_cases k <;> decide

theorem coordinateTotals : ((List.range 9).map coordinateInstructions).sum=1252 ∧
    ((List.range 9).map coordinateCycles).sum=1429 := by decide
#print axioms localW_bounds
#print axioms topDest_bound
#print axioms coordinateTotals
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateCode (im : Image) (k : Nat) : Prop where
  entry : CodeAt im (pcOf (entryStart k)) (entryWords k)
  values : ValuesCode im (valueStart k)
  plan : CodeAt im (pcOf (planStart k)) planCode
  paths : PathsCode im (pathStart k)
  sixth : ¬firstCoord k → CodeAt im (pcOf (valueStart k+110)) sixthCode
  top : CodeAt im (pcOf (topStart k)) (topWords k)
def CoordinateW (k child A : Nat) : Prop := LocalW (coordRegion k) child A ∨ A=topDest k child ∨ A=topDest k child+8
structure CoordinatePost (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  pc : t.pc=pcOf (nextEntry k)
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(688-64*i)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+720+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 52 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))
  regs : RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame : Frame s t (CoordinateW k child)
theorem coordinate_steps {im : Image} (k : Fin 9) (hc : CoordinateCode im k.val)
    (s : MachineState) (hp : s.pc=pcOf (entryStart k.val)) (raw : Fin 128)
    (hraw : s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes : ∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=
      BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j)) :
    ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧
      CoordinatePost s k.val (coordPhysical k.val raw.val) t := by
  let child : Fin 128 := ⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  change ∃t,Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t ∧ CoordinatePost s k.val child.val t
  have rb:=coordRegion_bounds k
  have sb:=coordSource_bounds k
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 (by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide : 0<32);omega) (by simp)]
    exact hbytes j hj)
  obtain ⟨t,vt,tp,tt,tr,tf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17])
  have td:=topDest_bound k child
  have local_eq : ∀A,coordRegion k.val ≤ A → A<2^64 → t.getMem (BitVec.ofNat 64 A)=v.getMem (BitVec.ofNat 64 A) := by
    intro A hA hi
    exact tf.get hi (by omega)
  have bf : Frame s v (LocalW (coordRegion k.val) child.val) :=
    (uf.trans hv.frame).mono (by intro A hA h;exact h.elim False.elim id)
  refine ⟨t,((su.trans uv).trans vt).of_eq (by rfl) (by unfold coordinateCycles;omega),tp,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [local_eq _ (by omega) (by omega),hv.values i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi hip half hh
    rw [local_eq _ (by omega) (by omega),hv.ends i hi hip half hh]
    exact uf.get (by omega) (by simp)
  · intro i hi half hh
    have pd:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val ≤ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧
      pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16 ≤ coordRegion k.val+320 at pd
    rw [local_eq _ (by omega) (by omega),hv.paths i hi half hh]
    exact uf.get (by omega) (by simp)
  · intro hn half hh
    have ph:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    rw [local_eq _ (by unfold destination;omega) (by unfold destination;omega),hv.sixth hn half hh]
    exact uf.get (by omega) (by simp)
  · intro half hh
    rw [tt half hh]
    have hb : topInput k.val ≤192 := by unfold topInput;split_ifs <;> omega
    apply bf.get (by omega)
    intro hw
    have h:=localW_bounds (coordRegion k.val) child _ hw
    omega
  · exact ((ur.trans hv.regs).trans tr).mono (by simp)
  · exact (bf.trans tf).mono (by intro A hA h;exact h)
#print axioms coordinate_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem localW_pad (region : Nat) (child : Fin 128) (half : Fin 2) (right : Bool) :
    ¬LocalW region child.val (region+(if right then 144 else 720)+8*half.val) := by
  intro h
  rcases h with (h|h)|h
  · obtain ⟨i,hi,h⟩:=h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · obtain ⟨i,hi,h⟩:=h
    have hs:=((Packing.scatterSafe child).1 ⟨i,hi⟩)
    dsimp only at hs
    have hmod : sibling child.val i %16=0 := by
      simp only [sibling,Nat.add_mod,Nat.mul_mod,show 48%16=0 from rfl,zero_mul,Nat.zero_mod,Nat.add_zero,hs.1]
    change (region+(if right then 144 else 720)+8*half.val=destination region (block child.val i/16) (child.val/2^i) ∨ region+(if right then 144 else 720)+8*half.val=destination region (block child.val i/16) (child.val/2^i)+8) at h
    rw [Packing.path_slot region child ⟨i,hi⟩] at h
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega
  · unfold SixthW destination at h
    have:=Nat.mod_lt (child.val/32) (by decide : 0<2)
    cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true] at h <;> omega

theorem localW_pads (region : Nat) (child : Fin 128) (A : Nat)
    (ha:A=region+144 ∨ A=region+152 ∨ A=region+720 ∨ A=region+728) : ¬LocalW region child.val A := by
  rcases ha with rfl|rfl|rfl|rfl
  · exact localW_pad region child 0 true
  · simpa [Nat.add_assoc] using localW_pad region child 1 true
  · exact localW_pad region child 0 false
  · simpa [Nat.add_assoc] using localW_pad region child 1 false

theorem topDest_prev (k : Fin 8) (child : Fin 128) :
    topDest k.val child.val=coordRegion (k.val+1)+144 ∨
    topDest k.val child.val=coordRegion (k.val+1)+720 := by
  have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
  have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
  fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8,coordRegion] <;> omega

theorem coordRegion_gap (j k : Fin 9) (hjk:j.val<k.val) :
    coordRegion k.val+896 ≤ coordRegion j.val := by
  unfold coordRegion
  omega

theorem coordinateW_bounds (k : Fin 9) (child : Fin 128) (A : Nat) (h:CoordinateW k.val child.val A) :
    1200 ≤ A ∧ A+8 ≤ coordRegion k.val+896 := by
  rcases h with h|h|h
  · have hb:=localW_bounds (coordRegion k.val) child A h
    have hr:=coordRegion_bounds k
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega
  · have hb:=topDest_bound k child
    have hlo : 1216 ≤ topDest k.val child.val := by
      have h32:=Nat.mod_lt (child.val/32) (by decide : 0<2)
      have h64:=Nat.mod_lt (child.val/64) (by decide : 0<2)
      fin_cases k <;> norm_num [topDest,topDest0,topDest1,topDest2,topDest3,topDest4,topDest5,topDest6,topDest7,topDest8] <;> omega
    omega

def ReadArea (k child A : Nat) : Prop :=
  (coordRegion k≤A ∧ A+8≤coordRegion k+896) ∨ A=topDest k child ∨ A=topDest k child+8

theorem readArea_disjoint (j k : Fin 9) (hj:j.val<k.val) (cj ck : Fin 128) (A : Nat)
    (ha:ReadArea j.val cj.val A) : ¬CoordinateW k.val ck.val A := by
  intro hw
  have wb:=coordinateW_bounds k ck A hw
  have gap:=coordRegion_gap j k hj
  rcases ha with ha|ha|ha
  · omega
  all_goals
    have j8:j.val<8 := by omega
    have jp : topDest j.val cj.val=coordRegion (j.val+1)+144 ∨ topDest j.val cj.val=coordRegion (j.val+1)+720 := topDest_prev ⟨j.val,j8⟩ cj
    have kd:=topDest_bound k ck
    by_cases hk:k.val=j.val+1
    · have rg : coordRegion k.val=coordRegion (j.val+1) := congrArg coordRegion hk
      rcases hw with hw|hw|hw
      · exact localW_pads (coordRegion k.val) ck A (by rcases jp with jp|jp <;> omega) hw
      · omega
      · omega
    · have g2:coordRegion k.val+896≤coordRegion (j.val+1) := by
        unfold coordRegion
        omega
      omega
#print axioms localW_pad
#print axioms readArea_disjoint
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
structure CoordinateReadout (s : MachineState) (k child : Nat) (t : MachineState) : Prop where
  values : ∀i<6,∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+(688-64*i)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  ends : ∀i<6,0 < i → ∀half<2,t.getMem (BitVec.ofNat 64 (coordRegion k+720+16*i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+16*i+8*half))
  paths : ∀i<5,∀half<2,t.getMem (BitVec.ofNat 64 (pathDestination (coordRegion k) child (packedSlots child) i+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+96+16*i+8*half))
  sixth : ¬firstCoord k → ∀half<2,t.getMem (BitVec.ofNat 64 (destination (coordRegion k) 52 (child/32)+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+176+8*half))
  top : ∀half<2,t.getMem (BitVec.ofNat 64 (topDest k child+8*half))=s.getMem (BitVec.ofNat 64 (coordSource k+topInput k+8*half))

theorem CoordinatePost.readout {s t : MachineState} {k child : Nat} (h:CoordinatePost s k child t) :
    CoordinateReadout s k child t := ⟨h.values,h.ends,h.paths,h.sixth,h.top⟩

theorem CoordinateReadout.congr {s u v : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout s k.val child.val u)
    (he:∀A,ReadArea k.val child.val A → v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val v := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.values i hi half hh
  · intro i hi hip half hh
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.ends i hi hip half hh
  · intro i hi half hh
    have hb:=Packing.path_slot_bound (coordRegion k.val) child ⟨i,hi⟩
    change coordRegion k.val≤pathDestination (coordRegion k.val) child.val (packedSlots child.val) i ∧ pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+16≤coordRegion k.val+320 at hb
    rw [he _ (Or.inl ⟨by omega,by omega⟩)]
    exact h.paths i hi half hh
  · intro hn half hh
    have hm:=Nat.mod_lt (child.val/32) (by decide:0<2)
    rw [he _ (Or.inl ⟨by unfold destination;omega,by unfold destination;omega⟩)]
    exact h.sixth hn half hh
  · intro half hh
    rw [he _ (Or.inr (by omega))]
    exact h.top half hh

theorem CoordinateReadout.source {s u t : MachineState} (k : Fin 9) (child : Fin 128)
    (h:CoordinateReadout u k.val child.val t)
    (he:∀A,coordSource k.val≤A → A<coordSource k.val+208 → u.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) :
    CoordinateReadout s k.val child.val t := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi half hh
    rw [h.values i hi half hh,he _ (by omega) (by omega)]
  · intro i hi hip half hh
    rw [h.ends i hi hip half hh,he _ (by omega) (by omega)]
  · intro i hi half hh
    rw [h.paths i hi half hh,he _ (by omega) (by omega)]
  · intro hn half hh
    rw [h.sixth hn half hh,he _ (by omega) (by omega)]
  · intro half hh
    have hb:topInput k.val≤192:=by unfold topInput;split_ifs <;>omega
    rw [h.top half hh,he _ (by omega) (by omega)]
#print axioms CoordinateReadout.congr
#print axioms CoordinateReadout.source
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem steps_same {im:Image} {s t u:MachineState} {n c d:Nat}
    (h:Steps im s n c t) (h':Steps im s n d u) : t=u := by
  induction h generalizing d u with
  | refl => cases h';rfl
  | @step s v t ins n c hf hs tail ih =>
    cases h' with
    | @step s' v' u' ins' n' d' hf' hs' tail' =>
      have he:ins'=ins:=Option.some.inj (hf'.symm.trans hf)
      subst ins'
      have hv:v'=v:=Option.some.inj (hs'.symm.trans hs)
      subst v'
      exact ih tail'

def PreciseBodyW (k child A:Nat) : Prop :=
  PayloadW (coordRegion k) child (packedSlots child) A ∨ (¬firstCoord k ∧ SixthW (coordRegion k) child A)

def PreciseCoordinateW (k child A:Nat) : Prop := PreciseBodyW k child A ∨ A=topDest k child ∨ A=topDest k child+8

theorem body_frame_exact {im:Image} (k:Fin 9) (hv:ValuesCode im (valueStart k.val))
    (hp:CodeAt im (pcOf (planStart k.val)) planCode) (hd:PathsCode im (pathStart k.val))
    (hx:¬firstCoord k.val → CodeAt im (pcOf (valueStart k.val+110)) sixthCode)
    (s t:MachineState) (hpc:s.pc=pcOf (valueStart k.val)) (child:Fin 128)
    (h8:s.getReg .x8=BitVec.ofNat 64 (coordRegion k.val)) (h16:s.getReg .x16=BitVec.ofNat 64 child.val)
    (h17:s.getReg .x17=BitVec.ofNat 64 (coordSource k.val))
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j))
    (hst:Steps im s (bodyInstructions k.val) (bodyCycles k.val) t) : Frame s t (PreciseBodyW k.val child.val) := by
  by_cases ha:firstCoord k.val
  · have hb : valueStart k.val=45266 ∨ valueStart k.val=45400 ∨ valueStart k.val=45543 ∨ valueStart k.val=45677 ∨ valueStart k.val=45820 ∨ valueStart k.val=45954 ∨ valueStart k.val=46097 ∨ valueStart k.val=46231 ∨ valueStart k.val=46376 := by fin_cases k <;> decide
    have hpl:valueStart k.val+34=planStart k.val:=by fin_cases k <;>decide
    have hpa:valueStart k.val+40=pathStart k.val:=by fin_cases k <;>decide
    have rb:=coordRegion_bounds k
    have sb:=coordSource_bounds k
    obtain ⟨u,su,hu⟩:=payload_packed hb hv (by rw [hpl];exact hp) (by rw [hpa];exact hd)
      s hpc (coordRegion k.val) (coordSource k.val) child rb.1 rb.2.1 rb.2.2 sb.1 sb.2.1 sb.2.2 h8 h16 h17 hbytes
    have ht:u=t:=steps_same su (by simpa [bodyInstructions,bodyCycles,ha] using hst)
    subst t
    exact hu.frame.mono (by intro A hA h;exact Or.inl h)
  · obtain ⟨u,su,hu⟩:=body_steps k hv hp hd hx s hpc child h8 h16 h17 hbytes
    have ht:u=t:=steps_same su hst
    subst t
    exact hu.frame.mono (by intro A hA h;rcases h with h|h;exact Or.inl h;exact Or.inr ⟨ha,h⟩)

theorem coordinate_frame_exact {im:Image} (k:Fin 9) (hc:CoordinateCode im k.val)
    (s t:MachineState) (hp:s.pc=pcOf (entryStart k.val)) (raw:Fin 128)
    (hraw:s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 raw.val)
    (hbytes:∀j<5,s.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val raw.val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val raw.val) j))
    (hst:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) t) :
    Frame s t (PreciseCoordinateW k.val (coordPhysical k.val raw.val)) := by
  let child:Fin 128:=⟨coordPhysical k.val raw.val,coordPhysical_lt k.val raw⟩
  obtain ⟨u,su,up,u16,u8,u17,ur,uf⟩:=entry_setup k hc.entry s hp raw hraw
  have hbytesu:∀j<5,u.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j) := by
    intro j hj
    rw [uf.getByte (by have:=Nat.mod_lt child.val (by decide:0<32);omega) (by simp)]
    exact hbytes j hj
  obtain ⟨v,uv,hv⟩:=body_steps k hc.values hc.plan hc.paths hc.sixth u up child u8 u16 u17 hbytesu
  have hf:=body_frame_exact k hc.values hc.plan hc.paths hc.sixth u v up child u8 u16 u17 hbytesu uv
  have sb:=coordSource_bounds k
  obtain ⟨z,vz,zp,zt,zr,zf⟩:=top_copy k hc.top v hv.pc (coordSource k.val) child sb.1 sb.2.1 sb.2.2
    (by rw [hv.regs.get (by decide),u16]) (by rw [hv.regs.get (by decide),u17])
  have hsz:Steps im s (coordinateInstructions k.val) (coordinateCycles k.val) z:=((su.trans uv).trans vz).of_eq (by rfl) (by unfold coordinateCycles;omega)
  have hz:z=t:=steps_same hsz hst
  subst t
  exact ((uf.trans hf).trans zf).mono (by intro A hA h;rcases h with (h|h)|h;exact h.elim;exact Or.inl h;exact Or.inr h)
#print axioms steps_same
#print axioms body_frame_exact
#print axioms coordinate_frame_exact
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.Research.SharedPathPacking
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def scatterPC (n:Nat) : Nat := if n<9 then entryStart n else 46509
def ScatterW (A:Nat) : Prop := 1200≤A ∧ A<9472
structure ScatterInv (s : MachineState) (raw:Fin 9 → Fin 128) (n:Nat) (t:MachineState) : Prop where
  pc:t.pc=pcOf (scatterPC n)
  readout:∀k:Fin 9,k.val<n → CoordinateReadout s k.val (coordPhysical k.val (raw k).val) t
  regs:RegsExcept s t [.x6,.x7,.x8,.x16,.x17,.x18,.x28]
  frame:Frame s t ScatterW
  exactFrame:Frame s t (fun A=>∃k:Fin 9,k.val<n ∧ PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A)

def RawAt (s:MachineState) (raw:Fin 9 → Fin 128) : Prop := ∀k:Fin 9,
  s.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val

def PlanAt (s:MachineState) : Prop := ∀child:Fin 128,∀j<5,
  s.getByte (BitVec.ofNat 64 (16748432+5*(child.val%32)+j))=BitVec.ofNat 8 (packedSlots child.val j)

theorem ScatterInv.next {im:Image} {s t:MachineState} {raw:Fin 9 → Fin 128} (k:Fin 9)
    (hc:CoordinateCode im k.val) (hr:RawAt s raw) (hp:PlanAt s) (hi:ScatterInv s raw k.val t) :
    ∃u,Steps im t (coordinateInstructions k.val) (coordinateCycles k.val) u ∧ ScatterInv s raw (k.val+1) u := by
  have hrawaddr : 9472≤rawAddress k.val ∧ rawAddress k.val<2^64 := by fin_cases k <;> decide
  have hraw : t.getMem (BitVec.ofNat 64 (rawAddress k.val)) >>> rawShift k.val &&& 127#64=BitVec.ofNat 64 (raw k).val := by
    rw [hi.frame.get hrawaddr.2 (by unfold ScatterW;omega)]
    exact hr k
  have hpc:t.pc=pcOf (entryStart k.val):=by simpa [scatterPC,k.isLt] using hi.pc
  have hbytes:∀j<5,t.getByte (BitVec.ofNat 64 (16748432+5*(coordPhysical k.val (raw k).val%32)+j))=BitVec.ofNat 8 (packedSlots (coordPhysical k.val (raw k).val) j) := by
    intro j hj
    rw [hi.frame.getByte (by have:=Nat.mod_lt (coordPhysical k.val (raw k).val) (by decide:0<32);omega) (by unfold ScatterW;omega)]
    exact hp ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ j hj
  obtain ⟨u,tu,hu⟩:=coordinate_steps k hc t hpc (raw k) hraw hbytes
  have hprecise:=coordinate_frame_exact k hc t u hpc (raw k) hraw hbytes tu
  have hw : ∀A,A<2^64 → CoordinateW k.val (coordPhysical k.val (raw k).val) A → ScatterW A := by
    intro A hA hw
    have hb:=coordinateW_bounds k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ A hw
    have rb:=coordRegion_bounds k
    unfold ScatterW
    omega
  refine ⟨u,tu,?_,?_,(hi.regs.trans hu.regs).mono (by simp),(hi.frame.trans (hu.frame.mono hw)).mono (by intro A hA h;exact h.elim id id),?_⟩
  · have he:nextEntry k.val=scatterPC (k.val+1) := by fin_cases k <;> decide
    simpa [he] using hu.pc
  · intro j hj
    by_cases he:j.val=k.val
    · have je:j=k:=Fin.ext he
      subst j
      apply CoordinateReadout.source k ⟨coordPhysical k.val (raw k).val,coordPhysical_lt k.val (raw k)⟩ hu.readout
      intro A ha hb
      have sb:=coordSource_bounds k
      exact hi.frame.get (by omega) (by unfold ScatterW;omega)
    · have hjk:j.val<k.val:=by omega
      apply (hi.readout j hjk).congr j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩
      intro A ha
      have hA:A<2^64 := by
        rcases ha with ha|ha|ha
        · have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
        · have td:=topDest_bound j ⟨coordPhysical j.val (raw j).val,coordPhysical_lt j.val (raw j)⟩;have rb:=coordRegion_bounds j;omega
      exact hu.frame.get hA (readArea_disjoint j k hjk ⟨_,coordPhysical_lt j.val (raw j)⟩ ⟨_,coordPhysical_lt k.val (raw k)⟩ A ha)
  · exact (hi.exactFrame.trans hprecise).mono (by
      intro A hA h
      rcases h with ⟨j,hj,h⟩|h
      · exact ⟨j,by omega,h⟩
      · exact ⟨k,by omega,h⟩)

def scatterInstructions (n:Nat) : Nat := ((List.range n).map coordinateInstructions).sum
def scatterCycles (n:Nat) : Nat := ((List.range n).map coordinateCycles).sum

theorem scatter_steps {im:Image} (hc:∀k:Fin 9,CoordinateCode im k.val) (s:MachineState)
    (raw:Fin 9 → Fin 128) (hr:RawAt s raw) (hp:PlanAt s) (hpc:s.pc=pcOf 45257) :
    ∃t,Steps im s 1252 1429 t ∧ ScatterInv s raw 9 t := by
  have hn : ∀n,n≤9 → ∃t,Steps im s (scatterInstructions n) (scatterCycles n) t ∧ ScatterInv s raw n t := by
    intro n
    induction n with
    | zero =>
      intro hn
      exact ⟨s,Steps.refl s,hpc,fun k hk=>by omega,RegsExcept.refl _ _,Frame.refl _ _,Frame.refl _ _⟩
    | succ n ih =>
      intro hn
      obtain ⟨t,st,ht⟩:=ih (by omega)
      obtain ⟨u,tu,hu⟩:=ht.next ⟨n,by omega⟩ (hc ⟨n,by omega⟩) hr hp
      refine ⟨u,?_,hu⟩
      simpa [scatterInstructions,scatterCycles,List.range_succ] using st.trans tu
  simpa [scatterInstructions,scatterCycles,coordinateTotals.1,coordinateTotals.2] using hn 9 (by decide)
#print axioms ScatterInv.next
#print axioms scatter_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv
set_option maxHeartbeats 1000000
theorem coordinateCodes {im:Image}
    (he:∀k:Fin 9,CodeAt im (pcOf (entryStart k.val)) (entryWords k.val))
    (hv:∀k:Fin 9,ValuesCode im (valueStart k.val))
    (hp:∀k:Fin 9,CodeAt im (pcOf (planStart k.val)) planCode)
    (hd:∀k:Fin 9,PathsCode im (pathStart k.val))
    (hx:∀k:Fin 5,CodeAt im (pcOf (sixthStart k.val)) sixthCode)
    (ht:∀k:Fin 9,CodeAt im (pcOf (topStart k.val)) (topWords k.val)) :
    ∀k:Fin 9,CoordinateCode im k.val := by
  intro k
  refine ⟨he k,hv k,hp k,hd k,?_,ht k⟩
  intro hn
  fin_cases k <;> simp only [firstCoord] at hn
  · exact (hn (by decide)).elim
  · exact hx 0
  · exact (hn (by decide)).elim
  · exact hx 1
  · exact (hn (by decide)).elim
  · exact hx 2
  · exact (hn (by decide)).elim
  · exact hx 3
  · exact hx 4
#print axioms coordinateCodes
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

theorem installed_coordinates : ∀k:Fin 9,CoordinateCode Images.expandImage k.val :=
  coordinateCodes installed_entry installed_values installed_plan installed_paths installed_sixth installed_top
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000

theorem CoordinateReadout.eq_written {s u v : MachineState} {k child : Nat}
    (hu : CoordinateReadout s k child u) (hv : CoordinateReadout s k child v)
    (A : Nat) (hA : PreciseCoordinateW k child A) :
    u.getMem (BitVec.ofNat 64 A)=v.getMem (BitVec.ofNat 64 A) := by
  rcases hA with ((h|h)|h)|h|h
  · obtain ⟨i,hi,h⟩ := h
    rcases h with h|h|⟨hip,h|h⟩
    · subst A
      exact (hu.values i hi 0 (by decide)).trans (hv.values i hi 0 (by decide)).symm
    · have he : coordRegion k+(696-64*i)=coordRegion k+(688-64*i)+8 := by omega
      rw [h,he]
      exact (hu.values i hi 1 (by decide)).trans (hv.values i hi 1 (by decide)).symm
    · subst A
      exact (hu.ends i hi hip 0 (by decide)).trans (hv.ends i hi hip 0 (by decide)).symm
    · have he : coordRegion k+728+16*i=coordRegion k+720+16*i+8 := by omega
      rw [h,he]
      exact (hu.ends i hi hip 1 (by decide)).trans (hv.ends i hi hip 1 (by decide)).symm
  · obtain ⟨i,hi,h|h⟩ := h
    · subst A
      exact (hu.paths i hi 0 (by decide)).trans (hv.paths i hi 0 (by decide)).symm
    · subst A
      exact (hu.paths i hi 1 (by decide)).trans (hv.paths i hi 1 (by decide)).symm
  · obtain ⟨hn,h|h⟩ := h
    · subst A
      exact (hu.sixth hn 0 (by decide)).trans (hv.sixth hn 0 (by decide)).symm
    · subst A
      exact (hu.sixth hn 1 (by decide)).trans (hv.sixth hn 1 (by decide)).symm
  · subst A
    exact (hu.top 0 (by decide)).trans (hv.top 0 (by decide)).symm
  · subst A
    exact (hu.top 1 (by decide)).trans (hv.top 1 (by decide)).symm

theorem ScatterInv.memory_eq {s t u : MachineState} {raw : Fin 9 → Fin 128}
    (hi : ScatterInv s raw 9 t)
    (hu : ∀k : Fin 9,CoordinateReadout s k.val (coordPhysical k.val (raw k).val) u)
    (hbackground : ∀A,A<2^64 →
      (¬∃k : Fin 9,PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A) →
      s.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A)) :
    ∀A,A<2^64 → t.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A) := by
  intro A hA
  classical
  by_cases h : ∃k : Fin 9,PreciseCoordinateW k.val (coordPhysical k.val (raw k).val) A
  · obtain ⟨k,hk⟩ := h
    exact (hi.readout k k.isLt).eq_written (hu k) A hk
  · rw [hi.exactFrame.get hA (by simpa using h)]
    exact hbackground A hA h
#print axioms CoordinateReadout.eq_written
#print axioms ScatterInv.memory_eq
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M
open SigGolfCandidate.Research.SharedForest
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem inflated_coordinate_value (b : SharedCodec.CBytes) (k : Fin 9) (i : Fin 6) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (1+13*k.val+i.val)=
      Paired.coordinateValues (SharedCodec.sigDecC b).forest k i := by
  fin_cases k <;> fin_cases i <;> rfl

theorem inflated_coordinate_path (b : SharedCodec.CBytes) (k : Fin 9) (level : Nat)
    (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (1+13*k.val+6+level)=
      Paired.coordinatePath (SharedCodec.sigDecC b).forest k level := by
  fin_cases k <;> norm_num at hl
  all_goals interval_cases level <;> rfl
#print axioms inflated_coordinate_value
#print axioms inflated_coordinate_path
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def afterCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x20e3303,0x7a031a63]
sym_block afterRun := symRun { noAlias := true } afterCode (pcOf 46509) 20

theorem after_steps {im : Image} (hc : CodeAt im (pcOf 46509) afterCode)
    (s : MachineState) (hpc : s.pc=pcOf 46509) :
    ∃t, Steps im s 4 4 t ∧
      t.pc=(if s.getMem 417824=0 then pcOf 46513 else pcOf 47005) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound afterRun hc s hpc (by simp [afterRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,afterRun.res]
    t3n []
    split_ifs <;> simp_all [pcOf]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    rfl

def finishCode : List (BitVec 32) := bv_list% 32 [0x66e37,0xe0e13,0x18e3303,0x4c000e93,0x26eb023,0x100293,0x513]
sym_block finishRun := symRun { noAlias := true } finishCode (pcOf 47005) 20

theorem finish_steps {im : Image} (hc : CodeAt im (pcOf 47005) finishCode)
    (s : MachineState) (hpc : s.pc=pcOf 47005) :
    ∃t, Steps im s 7 7 t ∧ t.pc=pcOf 47012 ∧
      t.getMem 1248=s.getMem 417816 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      RegsExcept s t [.x5,.x6,.x10,.x28,.x29] ∧ Frame s t (fun A=>A=1248) := by
  refine ⟨_,symRun_sound finishRun hc s hpc (by simp [finishRun.res,rv_simp]),?_,?_,?_,?_,?_,?_⟩
  · rfl
  · simp [finishRun.res,rv_simp]
  · rfl
  · rfl
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,finishRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA),if_neg hn]
#print axioms after_steps
#print axioms finish_steps
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.Research.SharedPathPacking W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem coordRegion_source (k : Fin 9) : coordRegion k.val=1216+V3.regionOffset k.val := by
  fin_cases k <;> rfl

theorem coordPhysical_source (k raw : Nat) : coordPhysical k raw=SharedV3.physical k raw := by
  simp [coordPhysical,SharedV3.physical,SharedV3.first,SigGolfCandidate.Research.SharedForest.physicalChild]

theorem pathDestination_source (k : Fin 9) (child : Fin 128) (level : Fin 5) :
    pathDestination (coordRegion k.val) child.val (packedSlots child.val) level.val=
      1216+V3.regionOffset k.val+SharedV3.sibOff child.val level.val := by
  change destination (coordRegion k.val) (block child.val level.val/16) (child.val/2^level.val)=_
  rw [Packing.path_slot,coordRegion_source]
  simp only [sibling,bitAt,SharedV3.sibOff,SharedV3.blkOff,if_pos level.isLt]

theorem sixthDestination_source (k : Fin 9) (child : Fin 128) :
    destination (coordRegion k.val) 52 (child.val/32)=
      1216+V3.regionOffset k.val+SharedV3.sibOff child.val 5 := by
  rw [coordRegion_source]
  simp [destination,SharedV3.sibOff,SharedV3.blkOff,Nat.add_assoc]

theorem topDest_source (k : Fin 9) (child : Fin 128) :
    topDest k.val child.val=1216+SharedV3.topOtherOff k.val child.val := by
  have h : ∀k : Fin 9,∀child : Fin 128,
      topDest k.val child.val=1216+SharedV3.topOtherOff k.val child.val := by
    intro k;fin_cases k <;> decide +kernel
  exact h k child

theorem chainDestination_source (k : Fin 9) (i : Fin 6) :
    coordRegion k.val+(688-64*i.val)=1216+(V3.chainOffset k.val i.val+48) := by
  rw [coordRegion_source]
  simp only [V3.chainOffset]
  have := i.isLt
  omega

theorem leafDestination_source (k : Fin 9) (i : Fin 6) (hi : 0 < i.val) :
    coordRegion k.val+720+16*i.val=1216+(V3.regionOffset k.val+V3.leafSlot i.val) := by
  rw [coordRegion_source]
  simp [V3.leafSlot,Nat.ne_of_gt hi,Nat.add_assoc]

theorem topInput_source (k : Fin 9) : topInput k.val=96+16*(SharedV3.lastLevel k.val+1) := by
  fin_cases k <;> rfl
#print axioms pathDestination_source
#print axioms topDest_source
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

structure SourceReadout (w : W9Machine.WBytes) (s : MachineState) (k child : Nat) : Prop where
  values : ∀i<6,DigAt s (coordSource k+16*i) (wdig w (V3.chainOffset k i+48))
  ends : ∀i<6,0 < i → DigAt s (coordSource k+16*i) (wdig w (V3.regionOffset k+V3.leafSlot i))
  paths : ∀i<5,DigAt s (coordSource k+96+16*i) (wdig w (V3.regionOffset k+SharedV3.sibOff child i))
  sixth : ¬firstCoord k → DigAt s (coordSource k+176) (wdig w (V3.regionOffset k+SharedV3.sibOff child 5))
  top : DigAt s (coordSource k+topInput k) (wdig w (SharedV3.topOtherOff k child))

theorem orig_word {w : W9Machine.WBytes} {t : MachineState} (off half : Nat) (hh : half<2)
    (hm : t.getMem (BitVec.ofNat 64 (1216+off+8*half))=(wdig w off).extractLsb' (64*half) 64) :
    OrigW w t (1216+off+8*half) := by
  unfold OrigW
  rw [hm]
  interval_cases half
  · simpa using (W9Machine.wdig_lo w off)
  · simpa [Nat.add_assoc] using (W9Machine.wdig_hi w off)

theorem digAt_half {t : MachineState} {A : Nat} {d : BitVec 128} (h : DigAt t A d)
    (half : Nat) (hh : half<2) :
    t.getMem (BitVec.ofNat 64 (A+8*half))=d.extractLsb' (64*half) 64 := by
  interval_cases half
  · simpa using h.1
  · simpa using h.2

theorem CoordinateReadout.original {s t : MachineState} {w : W9Machine.WBytes}
    (k : Fin 9) (child : Fin 128) (h : CoordinateReadout s k.val child.val t)
    (hs : SourceReadout w s k.val child.val) (A : Nat) (hA : PreciseCoordinateW k.val child.val A) :
    OrigW w t A := by
  have hv : ∀i<6,∀half<2,OrigW w t (coordRegion k.val+(688-64*i)+8*half) := by
    intro i hi half hh
    rw [chainDestination_source k ⟨i,hi⟩]
    apply orig_word _ half hh
    rw [←chainDestination_source k ⟨i,hi⟩,h.values i hi half hh]
    exact digAt_half (hs.values i hi) half hh
  have he : ∀i<6,0 < i → ∀half<2,OrigW w t (coordRegion k.val+720+16*i+8*half) := by
    intro i hi hip half hh
    rw [leafDestination_source k ⟨i,hi⟩ hip]
    apply orig_word _ half hh
    rw [←leafDestination_source k ⟨i,hi⟩ hip,h.ends i hi hip half hh]
    exact digAt_half (hs.ends i hi hip) half hh
  have hp : ∀i<5,∀half<2,OrigW w t (pathDestination (coordRegion k.val) child.val (packedSlots child.val) i+8*half) := by
    intro i hi half hh
    rw [pathDestination_source k child ⟨i,hi⟩]
    rw [Nat.add_assoc 1216]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 1216,←pathDestination_source k child ⟨i,hi⟩,h.paths i hi half hh]
    exact digAt_half (hs.paths i hi) half hh
  have h6 : ¬firstCoord k.val → ∀half<2,OrigW w t (destination (coordRegion k.val) 52 (child.val/32)+8*half) := by
    intro hn half hh
    rw [sixthDestination_source k child,Nat.add_assoc 1216]
    apply orig_word _ half hh
    rw [←Nat.add_assoc 1216,←sixthDestination_source k child,h.sixth hn half hh]
    exact digAt_half (hs.sixth hn) half hh
  have ht : ∀half<2,OrigW w t (topDest k.val child.val+8*half) := by
    intro half hh
    rw [topDest_source k child]
    apply orig_word _ half hh
    rw [←topDest_source k child,h.top half hh]
    exact digAt_half hs.top half hh
  rcases hA with ((ha|ha)|ha)|ha|ha
  · obtain ⟨i,hi,ha⟩:=ha
    rcases ha with ha|ha|⟨hip,ha|ha⟩
    · subst A;simpa using hv i hi 0 (by decide)
    · rw [ha,show coordRegion k.val+(696-64*i)=coordRegion k.val+(688-64*i)+8 by omega]
      simpa using hv i hi 1 (by decide)
    · subst A;simpa using he i hi hip 0 (by decide)
    · rw [ha,show coordRegion k.val+728+16*i=coordRegion k.val+720+16*i+8 by omega]
      simpa using he i hi hip 1 (by decide)
  · obtain ⟨i,hi,ha|ha⟩:=ha
    · subst A;simpa using hp i hi 0 (by decide)
    · subst A;simpa using hp i hi 1 (by decide)
  · obtain ⟨hn,ha|ha⟩:=ha
    · subst A;simpa using h6 hn 0 (by decide)
    · subst A;simpa using h6 hn 1 (by decide)
  · subst A;simpa using ht 0 (by decide)
  · subst A;simpa using ht 1 (by decide)
#print axioms CoordinateReadout.original
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def words : List (BitVec 32) := [0xe3023,0x8e0e13,0xffde6ce3]
sym_block zeroRun := symRun {noAlias:=true} words (pcOf 45254) 10

def result (p : Word) : Result :=
  ⟨zeroRun.res.st,
    .ite .ltu (.bin .add (.reg .x28) (.c 8)) (.reg .x29)
      (.c (((p+4)+4)+18446744073709551608)) (.c (((p+4)+4)+4)),.branch,3,3⟩
theorem checked (p : Word) : symRun {noAlias:=true} words p 10=some (result p) := by krfl

theorem step {im : Image} (p : Word) (hc : CodeAt im p words)
    (s : MachineState) (hpc : s.pc=p) (A B : Nat)
    (ha : A%8=0) (hb : A+8≤B) (hB : B≤9472)
    (h28 : s.getReg .x28=BitVec.ofNat 64 A) (h29 : s.getReg .x29=BitVec.ofNat 64 B) :
    ∃t, Steps im s 3 3 t ∧ t.pc=(if A+8<B then p else p+12) ∧
      t.getReg .x28=BitVec.ofNat 64 (A+8) ∧ t.getMem (BitVec.ofNat 64 A)=0 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun x=>x=A) := by
  refine ⟨_,symRun_sound (checked p) hc s hpc ?_,?_,?_,?_,?_,?_⟩
  · simp [result,zeroRun.res,rv_simp,h28,accessValid_iff,MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc,result,E.eval,BinOp.eval,CmpOp.eval,h28,h29]
    rw [show (BitVec.ofNat 64 A+8 : Word)=BitVec.ofNat 64 (A+8) by simp [BitVec.ofNat_add]]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show A+8<2^64 by omega),Nat.mod_eq_of_lt (show B<2^64 by omega)]
    have hback : ((p+4)+4)+18446744073709551608=p := by
      simp only [BitVec.add_assoc]; change p+0=p;exact BitVec.add_zero p
    have hnext : ((p+4)+4)+4=p+12 := by simp only [BitVec.add_assoc];rfl
    rw [hback,hnext]
    split_ifs <;> simp_all
  · simp only [Result.toState_getReg,result,zeroRun.res]
    t3n [h28]
  · simp only [Result.toState_getMem,result,zeroRun.res]
    t3n [h28]
    simp
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro x hx hn
    simp only [Result.toState_getMem,result,zeroRun.res]
    t3n [h28]
    simp only [Nat.add_zero,Nat.mod_eq_of_lt (show x<18446744073709551616 by simpa using hx),Nat.mod_eq_of_lt (show A<18446744073709551616 by omega),if_neg hn]

theorem loop {im : Image} (p : Word) (hc : CodeAt im p words) (A : Nat) (ha : A%8=0) :
    ∀n (s : MachineState), A+8*(n+1)≤9472 → s.pc=p →
      s.getReg .x28=BitVec.ofNat 64 A → s.getReg .x29=BitVec.ofNat 64 (A+8*(n+1)) →
      ∃t,Steps im s (3*(n+1)) (3*(n+1)) t ∧ t.pc=p+12 ∧
        t.getReg .x28=BitVec.ofNat 64 (A+8*(n+1)) ∧
        (∀i<n+1,t.getMem (BitVec.ofNat 64 (A+8*i))=0) ∧
        RegsExcept s t [.x28] ∧ Frame s t (fun x=>A≤x ∧ x<A+8*(n+1)) := by
  intro n
  induction n generalizing A with
  | zero =>
    intro s hbound hp h28 h29
    obtain ⟨t,st,pt,rt,mt,rr,ff⟩:=step p hc s hp A (A+8) ha (by omega) (by omega) h28 (by simpa using h29)
    refine ⟨t,by simpa using st,?_,?_,?_,rr,ff.mono ?_⟩
    · simpa using pt
    · simpa using rt
    · intro i hi
      have : i=0 := by omega
      simpa [this] using mt
    · intro x hx he;omega
  | succ n ih =>
    intro s hbound hp h28 h29
    obtain ⟨u,su,pu,r28,mu,ru,fu⟩:=step p hc s hp A (A+8*(n+2)) ha (by omega) hbound h28 h29
    have hp' : u.pc=p := by simpa [show A+8<A+8*(n+2) by omega] using pu
    have h29' : u.getReg .x29=BitVec.ofNat 64 ((A+8)+8*(n+1)) := by
      rw [ru.get (by decide),h29]
      congr 1;omega
    obtain ⟨t,ut,pt,rt,mt,rr,ft⟩:=ih (A+8) (by omega) u (by omega) hp' r28 h29'
    refine ⟨t,?_,pt,?_,?_,(ru.trans rr).mono (by decide),?_⟩
    · convert su.trans ut using 1 <;> omega
    · convert rt using 2 <;> omega
    · intro i hi
      cases i with
      | zero => simpa using (ft.get (by omega) (by omega)).trans mu
      | succ i => simpa [Nat.mul_add,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using mt i (by omega)
    · exact (fu.trans ft).mono (by intro x hx h;rcases h with h|h <;> omega)
#print axioms checked
#print axioms step
#print axioms loop
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def acceptedCode : List (BitVec 32) := [0x66e37,0xe0e13,0x20e3023,0x13e3423,0x8bb03,0x21b5b13,0x16e3823,0x20eb7,0x550e8e93,0x16eb023,0x6000e93,0x8b303,0x6eb023,0x88b303,0x6eb423,0x108b303,0x6eb823,0x188b303,0x6ebc23,0x4c000e13,0x2eb7,0x500e8e93]
sym_block acceptedRun := symRun {noAlias:=true} acceptedCode (pcOf 45232) 100
def finalScatterCode : List (BitVec 32) := [0x4c000e13,0x20e3303,0x66eb7,0xe8e93,0x6ebc23,0x100313,0x26eb023,0x6000e13,0x20eb7,0x160e8e93,0xe3303,0x6eb023,0x8e3303,0x6eb423,0x10e3303,0x6eb823,0x18e3303,0x6ebc23,0x4c000e13,0x2eb7,0x500e8e93]
sym_block finalScatterRun := symRun {noAlias:=true} finalScatterCode (pcOf 46980) 100

theorem accepted_steps {im : Image} (hc : CodeAt im (pcOf 45232) acceptedCode)
    (s : MachineState) (hpc : s.pc=pcOf 45232) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 22 22 t ∧ t.pc=pcOf 45254 ∧
      t.getReg .x28=1216 ∧ t.getReg .x29=9472 ∧
      t.getMem 0x66020=0 ∧ t.getMem 0x66008=s.getReg .x19 ∧
      t.getMem 0x66010=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      (∀i<4,t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (0x20160+8*i))) ∧
      RegsExcept s t [.x6,.x22,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128)) := by
  refine ⟨_,symRun_sound acceptedRun hc s hpc ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [acceptedRun.res,rv_simp,h17,accessValid_iff,MEMORY_BYTES]
  · rfl
  · rfl
  · rfl
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · simp [acceptedRun.res,rv_simp,h17]
  · intro i hi
    interval_cases i <;> simp [acceptedRun.res,rv_simp,h17]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,acceptedRun.res]
    t3n [h17]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    split_ifs <;> first | rfl | omega

theorem finalScatter_steps {im : Image} (hc : CodeAt im (pcOf 46980) finalScatterCode)
    (s : MachineState) (hpc : s.pc=pcOf 46980) :
    ∃t,Steps im s 21 21 t ∧ t.pc=pcOf 47001 ∧
      t.getReg .x28=1216 ∧ t.getReg .x29=9472 ∧
      t.getMem 0x66018=s.getMem 1248 ∧ t.getMem 0x66020=1 ∧
      (∀i<4,t.getMem (BitVec.ofNat 64 (0x20160+8*i))=s.getMem (BitVec.ofNat 64 (96+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66018 ∨ A=0x66020 ∨ (0x20160≤A ∧ A<0x20180)) := by
  refine ⟨_,symRun_sound finalScatterRun hc s hpc ?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [finalScatterRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]
  · rfl
  · rfl
  · rfl
  · simp [finalScatterRun.res,rv_simp]
  · simp [finalScatterRun.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [finalScatterRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,finalScatterRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    split_ifs <;> first | rfl | omega
#print axioms accepted_steps
#print axioms finalScatter_steps
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def first0Code : List (BitVec 32) := [0x66e37,0xe0e13,0x40e3303,0x1536663]
sym_block first0Run := symRun {noAlias:=true} first0Code (pcOf 46933) 20
def zero0Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero0Run := symRun {noAlias:=true} zero0Code (pcOf 46937) 20
def sub0Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub0Run := symRun {noAlias:=true} sub0Code (pcOf 46939) 20
theorem first0_steps {im : Image} (hc : CodeAt im (pcOf 46933) first0Code)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46939 else pcOf 46937) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417856#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first0Run hc s hp (by simp [first0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first0Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first0Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero0_steps {im : Image} (hc : CodeAt im (pcOf 46937) zero0Code)
    (s : MachineState) (hp : s.pc=pcOf 46937) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero0Run hc s hp (by simp [zero0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub0_steps {im : Image} (hc : CodeAt im (pcOf 46939) sub0Code)
    (s : MachineState) (hp : s.pc=pcOf 46939) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub0Run hc s hp (by simp [sub0Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub0Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual0Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46933) first0Code
  zero : CodeAt im (pcOf 46937) zero0Code
  sub : CodeAt im (pcOf 46939) sub0Code

theorem residual0_steps {im : Image} [hc : Residual0Code im]
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417856=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46940 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first0_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub0_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero0_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual0_steps
def first1Code : List (BitVec 32) := [0x66e37,0xe0e13,0x48e3303,0x1536663]
sym_block first1Run := symRun {noAlias:=true} first1Code (pcOf 46949) 20
def zero1Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero1Run := symRun {noAlias:=true} zero1Code (pcOf 46953) 20
def sub1Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub1Run := symRun {noAlias:=true} sub1Code (pcOf 46955) 20
theorem first1_steps {im : Image} (hc : CodeAt im (pcOf 46949) first1Code)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46955 else pcOf 46953) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417864#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first1Run hc s hp (by simp [first1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first1Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first1Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero1_steps {im : Image} (hc : CodeAt im (pcOf 46953) zero1Code)
    (s : MachineState) (hp : s.pc=pcOf 46953) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero1Run hc s hp (by simp [zero1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub1_steps {im : Image} (hc : CodeAt im (pcOf 46955) sub1Code)
    (s : MachineState) (hp : s.pc=pcOf 46955) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub1Run hc s hp (by simp [sub1Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub1Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual1Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46949) first1Code
  zero : CodeAt im (pcOf 46953) zero1Code
  sub : CodeAt im (pcOf 46955) sub1Code

theorem residual1_steps {im : Image} [hc : Residual1Code im]
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417864=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46956 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first1_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub1_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero1_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual1_steps
def first2Code : List (BitVec 32) := [0x66e37,0xe0e13,0x50e3303,0x1536663]
sym_block first2Run := symRun {noAlias:=true} first2Code (pcOf 46966) 20
def zero2Code : List (BitVec 32) := [0xa93,0x80006f]
sym_block zero2Run := symRun {noAlias:=true} zero2Code (pcOf 46970) 20
def sub2Code : List (BitVec 32) := [0x406a8ab3]
sym_block sub2Run := symRun {noAlias:=true} sub2Code (pcOf 46972) 20
theorem first2_steps {im : Image} (hc : CodeAt im (pcOf 46966) first2Code)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t,Steps im s 4 4 t ∧ t.pc=(if C<R then pcOf 46972 else pcOf 46970) ∧
      t.getReg .x6=BitVec.ofNat 64 C ∧ RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (417872#64)=BitVec.ofNat 64 C at hm
  refine ⟨_,symRun_sound first2Run hc s hp (by simp [first2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · simp only [Result.toState_pc,first2Run.res]
    t3n [h21,hm]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hC,Nat.mod_eq_of_lt (show R<2^64 by omega)]
    simp only [decide_eq_true_eq]
    all_goals split_ifs <;> rfl
  · simp [first2Run.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem zero2_steps {im : Image} (hc : CodeAt im (pcOf 46970) zero2Code)
    (s : MachineState) (hp : s.pc=pcOf 46970) :
    ∃t,Steps im s 2 2 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=0 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound zero2Run hc s hp (by simp [zero2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem sub2_steps {im : Image} (hc : CodeAt im (pcOf 46972) sub2Code)
    (s : MachineState) (hp : s.pc=pcOf 46972) (R C : Nat) (hR : R≤63) (hC : C<R)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h6 : s.getReg .x6=BitVec.ofNat 64 C) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound sub2Run hc s hp (by simp [sub2Run.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,sub2Run.res]
    t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le R C (by omega) (by omega)
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

class Residual2Code (im : Image) : Prop where
  first : CodeAt im (pcOf 46966) first2Code
  zero : CodeAt im (pcOf 46970) zero2Code
  sub : CodeAt im (pcOf 46972) sub2Code

theorem residual2_steps {im : Image} [hc : Residual2Code im]
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C : Nat) (hR : R≤63) (hC : C<2^64)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (hm : s.getMem 417872=BitVec.ofNat 64 C) :
    ∃t n,n≤6 ∧ Steps im s n n t ∧ t.pc=pcOf 46973 ∧ t.getReg .x21=BitVec.ofNat 64 (R-C) ∧
      RegsExcept s t [.x6,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u6,ru,fu⟩:=first2_steps hc.first s hp R C hR hC h21 hm
  by_cases h : C<R
  · rw [if_pos h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=sub2_steps hc.sub u pu R C hR h (by rw [ru.get (by decide)];exact h21) u6
    exact ⟨t,5,by omega,su.trans st,pt,ht,(ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
  · rw [if_neg h] at pu
    obtain ⟨t,st,pt,ht,rr,ff⟩:=zero2_steps hc.zero u pu
    exact ⟨t,6,by omega,su.trans st,pt,by simpa [show R-C=0 by omega] using ht,
      (ru.trans rr).mono (by decide),(fu.trans ff).mono (by simp)⟩
#print axioms residual2_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def initCode : List (BitVec 32) := [0x66e37,0xe0e13,0xe3a03,0x3f00a93]
sym_block initRun := symRun {noAlias:=true} initCode (pcOf 46929) 100
def range1Code : List (BitVec 32) := [0x3000393,0x87afc63]
sym_block range1Run := symRun {noAlias:=true} range1Code (pcOf 46940) 100
def range2Code : List (BitVec 32) := [0x2300393,0x47afc63]
sym_block range2Run := symRun {noAlias:=true} range2Code (pcOf 46956) 100
def range3Code : List (BitVec 32) := [0x1200393,0x7afa63]
sym_block range3Run := symRun {noAlias:=true} range3Code (pcOf 46973) 100
def lookup1Code : List (BitVec 32) := [0xff9e37,0x390e0e13,0x15e0e33,0xe4303,0x1200393,0x27a7eb3,0x7d31e63]
sym_block lookup1Run := symRun {noAlias:=true} lookup1Code (pcOf 46942) 100
def lookup2Code : List (BitVec 32) := [0xff9e37,0x3d0e0e13,0x15e0e33,0xe4303,0x1200393,0x27a5eb3,0x27efeb3,0x3d31c63]
sym_block lookup2Run := symRun {noAlias:=true} lookup2Code (pcOf 46958) 100
def lastCode : List (BitVec 32) := [0x14400393,0x27a5eb3,0x1da9463]
sym_block lastRun := symRun {noAlias:=true} lastCode (pcOf 46975) 100
def goodCode : List (BitVec 32) := [0xea5fb06f]
sym_block goodRun := symRun {noAlias:=true} goodCode (pcOf 46978) 100
def badCode : List (BitVec 32) := [0xf7cd206f]
sym_block badRun := symRun {noAlias:=true} badCode (pcOf 46979) 100
theorem range1_steps {im : Image} (hc : CodeAt im (pcOf 46940) range1Code)
    (s : MachineState) (hp : s.pc=pcOf 46940) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<48 then pcOf 46942 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range1Run hc s hp (by simp [range1Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range1Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<48 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range1_steps
theorem range2_steps {im : Image} (hc : CodeAt im (pcOf 46956) range2Code)
    (s : MachineState) (hp : s.pc=pcOf 46956) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<35 then pcOf 46958 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range2Run hc s hp (by simp [range2Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range2Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<35 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range2_steps
theorem range3_steps {im : Image} (hc : CodeAt im (pcOf 46973) range3Code)
    (s : MachineState) (hp : s.pc=pcOf 46973) (R : Nat) (hR : R≤63)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 2 2 t ∧ t.pc=(if R<18 then pcOf 46975 else pcOf 46979) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound range3Run hc s hp (by simp [range3Run.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,range3Run.res]
    t3n [h21]
    simp only [BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show R<2^64 by omega),decide_eq_true_eq]
    by_cases h : R<18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms range3_steps
theorem init_steps {im : Image} (hc : CodeAt im (pcOf 46929) initCode)
    (s : MachineState) (hp : s.pc=pcOf 46929) (hints : Nat)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 hints) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 46933 ∧ t.getReg .x20=BitVec.ofNat 64 hints ∧
      t.getReg .x21=63 ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound initRun hc s hp (by simp [initRun.res,rv_simp]),rfl,?_,rfl,?_,?_⟩
  · simp [initRun.res,rv_simp,hm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms init_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open RiscvZkvm.Rv64
theorem rem18 (n : Nat) (hn : n<2^64) : rv64_remu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n%18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_remu,BitVec.toNat_umod,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n%18<2^64 by omega)]
  omega
theorem div18 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 18#64=BitVec.ofNat 64 (n/18) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/18<2^64 by omega)]
  omega
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def lookup1PreCode : List (BitVec 32) := [0xff9e37,0x390e0e13,0x15e0e33]
sym_block lookup1PreRun := symRun {noAlias:=true} lookup1PreCode (pcOf 46942) 100
def lookup1LoadCode : List (BitVec 32) := [0xe4303]
def lookup1PostCode : List (BitVec 32) := [0x1200393,0x27a7eb3,0x7d31e63]
sym_block lookup1PostRun := symRun {noAlias:=true} lookup1PostCode (pcOf 46946) 100
theorem lookup1_pre {im : Image} (hc : CodeAt im (pcOf 46942) lookup1PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46945 ∧ t.getReg .x28=BitVec.ofNat 64 (16749456+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PreRun hc s hp (by simp [lookup1PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup1PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup1_load {im : Image} (hc : CodeAt im (pcOf 46945) lookup1LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46945) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46946 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46946;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup1_post {im : Image} (hc : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46946) (H F : Nat) (hH : H<5832) (hF : F<18)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if F=H%18 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup1PostRun hc s hp (by simp [lookup1PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup1PostRun.res]
    t3n [h6,h20]
    simp only [div18 H (by omega),rem18 H (by omega),rem18 (H/18) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H%18)) ↔ F=H%18 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H%18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms lookup1_pre
#print axioms lookup1_load
#print axioms lookup1_post
def lookup2PreCode : List (BitVec 32) := [0xff9e37,0x3d0e0e13,0x15e0e33]
sym_block lookup2PreRun := symRun {noAlias:=true} lookup2PreCode (pcOf 46958) 100
def lookup2LoadCode : List (BitVec 32) := [0xe4303]
def lookup2PostCode : List (BitVec 32) := [0x1200393,0x27a5eb3,0x27efeb3,0x3d31c63]
sym_block lookup2PostRun := symRun {noAlias:=true} lookup2PostCode (pcOf 46962) 100
theorem lookup2_pre {im : Image} (hc : CodeAt im (pcOf 46958) lookup2PreCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R : Nat) (h21 : s.getReg .x21=BitVec.ofNat 64 R) :
    ∃t,Steps im s 3 3 t ∧ t.pc=pcOf 46961 ∧ t.getReg .x28=BitVec.ofNat 64 (16749520+R) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PreRun hc s hp (by simp [lookup2PreRun.res,rv_simp]),rfl,?_,?_,?_⟩
  · simp [lookup2PreRun.res,rv_simp,h21,BitVec.ofNat_add,add_comm]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem lookup2_load {im : Image} (hc : CodeAt im (pcOf 46961) lookup2LoadCode)
    (s : MachineState) (hp : s.pc=pcOf 46961) (a F : Nat) (ha : a+1≤2^24) (hF : F<256)
    (h28 : s.getReg .x28=BitVec.ofNat 64 a) (hm : s.getByte (BitVec.ofNat 64 a)=BitVec.ofNat 8 F) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 46962 ∧ t.getReg .x6=BitVec.ofNat 64 F ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  have hoff : s.getReg .x28+signExtend12 (0:BitVec 12)=BitVec.ofNat 64 a := by
    rw [h28];apply BitVec.eq_of_toNat_eq;simp [signExtend12]
  have st:=steps_lbu (rd:=.x6) (rs:=.x28) (off:=0) hc hp rfl
    (by rw [hoff,accessValid_iff,toNat_ofNat_lt (by omega)];simp [MEMORY_BYTES];omega)
  refine ⟨_,st,?_,?_,?_,?_⟩
  · show s.pc+4=pcOf 46962;rw [hp];rfl
  · rw [MachineState.getReg_setPC,MachineState.getReg_setReg_eq (by decide),hoff,hm]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.truncate_eq_setWidth,BitVec.toNat_setWidth,BitVec.toNat_ofNat]
    omega
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rw [MachineState.getReg_setPC,MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  · intro A hA hn;simp

theorem lookup2_post {im : Image} (hc : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46962) (H F : Nat) (hH : H<5832) (hF : F<18)
    (h6 : s.getReg .x6=BitVec.ofNat 64 F) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 4 10 t ∧ t.pc=(if F=H/18%18 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lookup2PostRun hc s hp (by simp [lookup2PostRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lookup2PostRun.res]
    t3n [h6,h20]
    simp only [div18 H (by omega),rem18 (H/18) (by omega)]
    have he : (BitVec.ofNat 64 F=BitVec.ofNat 64 (H/18%18)) ↔ F=H/18%18 := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : F=H/18%18 <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms lookup2_pre
#print axioms lookup2_load
#print axioms lookup2_post
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
theorem lookup1_steps {im : Image}
    (hpre : CodeAt im (pcOf 46942) lookup1PreCode)
    (hload : CodeAt im (pcOf 46945) lookup1LoadCode)
    (hpost : CodeAt im (pcOf 46946) lookup1PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46942) (R H F : Nat) (hR : R<48) (hH : H<5832) (hF : F<18)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749456+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 7 10 t ∧ t.pc=(if F=H%18 then pcOf 46949 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup1_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup1_load hload u pu (16749456+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup1_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
#print axioms lookup1_steps
theorem lookup2_steps {im : Image}
    (hpre : CodeAt im (pcOf 46958) lookup2PreCode)
    (hload : CodeAt im (pcOf 46961) lookup2LoadCode)
    (hpost : CodeAt im (pcOf 46962) lookup2PostCode)
    (s : MachineState) (hp : s.pc=pcOf 46958) (R H F : Nat) (hR : R<35) (hH : H<5832) (hF : F<18)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getByte (BitVec.ofNat 64 (16749520+R))=BitVec.ofNat 8 F) :
    ∃t,Steps im s 8 14 t ∧ t.pc=(if F=H/18%18 then pcOf 46966 else pcOf 46979) ∧
      RegsExcept s t [.x6,.x7,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u28,ru,fu⟩:=lookup2_pre hpre s hp R h21
  obtain ⟨v,sv,pv,v6,rv,fv⟩:=lookup2_load hload u pu (16749520+R) F (by omega) (by omega) u28
    (by rw [fu.getByte (by omega) (by simp)];exact hm)
  obtain ⟨t,st,pt,rt,ft⟩:=lookup2_post hpost v pv H F hH hF v6
    (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
  exact ⟨t,(su.trans sv).trans st,pt,((ru.trans rv).trans rt).mono (by decide),
    ((fu.trans fv).trans ft).mono (by simp)⟩
#print axioms lookup2_steps
theorem div324 (n : Nat) (hn : n<2^64) : rv64_divu (BitVec.ofNat 64 n) 324#64=BitVec.ofNat 64 (n/324) := by
  apply BitVec.eq_of_toNat_eq
  simp [rv64_divu,BitVec.toNat_udiv,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show n/324<2^64 by omega)]
  omega

theorem last_steps {im : Image} (hc : CodeAt im (pcOf 46975) lastCode)
    (s : MachineState) (hp : s.pc=pcOf 46975) (R H : Nat) (hR : R≤63) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H) :
    ∃t,Steps im s 3 6 t ∧ t.pc=(if H/324=R then pcOf 46978 else pcOf 46979) ∧
      RegsExcept s t [.x7,.x29] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound lastRun hc s hp (by simp [lastRun.res,rv_simp]),?_,?_,?_⟩
  · simp only [Result.toState_pc,lastRun.res]
    t3n [h21,h20]
    rw [div324 H (by omega)]
    have he : (BitVec.ofNat 64 R=BitVec.ofNat 64 (H/324)) ↔ H/324=R := by
      constructor
      · intro h;have:=congrArg BitVec.toNat h;simp only [BitVec.toNat_ofNat] at this;omega
      · intro h;rw [h]
    simp only [he]
    by_cases h : H/324=R <;> simp [h]
  · intro r hr;cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl

theorem good_steps {im : Image} (hc : CodeAt im (pcOf 46978) goodCode) (s : MachineState) (hp : s.pc=pcOf 46978) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 42795 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound goodRun hc s hp (by simp [goodRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
theorem bad_steps {im : Image} (hc : CodeAt im (pcOf 46979) badCode) (s : MachineState) (hp : s.pc=pcOf 46979) :
    ∃t,Steps im s 1 1 t ∧ t.pc=pcOf 354 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  exact ⟨_,symRun_sound badRun hc s hp (by simp [badRun.res,rv_simp]),rfl,fun r _=>by cases r <;> rfl,fun A _ _=>rfl⟩
#print axioms last_steps
#print axioms good_steps
#print axioms bad_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
structure Code (im : Image) : Prop where
  init : CodeAt im (pcOf 46929) initCode
  r0 : Residual0Code im
  r1 : Residual1Code im
  r2 : Residual2Code im
  range1 : CodeAt im (pcOf 46940) range1Code
  range2 : CodeAt im (pcOf 46956) range2Code
  range3 : CodeAt im (pcOf 46973) range3Code
  lookup1Pre : CodeAt im (pcOf 46942) lookup1PreCode
  lookup1Load : CodeAt im (pcOf 46945) lookup1LoadCode
  lookup1Post : CodeAt im (pcOf 46946) lookup1PostCode
  lookup2Pre : CodeAt im (pcOf 46958) lookup2PreCode
  lookup2Load : CodeAt im (pcOf 46961) lookup2LoadCode
  lookup2Post : CodeAt im (pcOf 46962) lookup2PostCode
  last : CodeAt im (pcOf 46975) lastCode
  good : CodeAt im (pcOf 46978) goodCode
  bad : CodeAt im (pcOf 46979) badCode

def regs : List Reg := [.x6,.x7,.x21,.x28,.x29]
theorem phase1_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46933) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417856#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<48 → T r<18)
    (hbytes : ∀ r,r<48 → s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤15 ∧ c≤18 ∧ Steps im s n c t ∧
      t.pc=(if R-C<48 ∧ H%18=T (R-C) then pcOf 46949 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r0
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual0_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range1_steps hc.range1 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<48
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup1_steps hc.lookup1Pre hc.lookup1Load hc.lookup1Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+7,n+2+10,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase1_steps
theorem phase2_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46949) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417864#64)=BitVec.ofNat 64 C)
    (T : Nat→Nat) (hT : ∀ r,r<35 → T r<18)
    (hbytes : ∀ r,r<35 → s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T r)) :
    ∃t n c,n≤16 ∧ c≤22 ∧ Steps im s n c t ∧
      t.pc=(if R-C<35 ∧ H/18%18=T (R-C) then pcOf 46966 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r1
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual1_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range2_steps hc.range2 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<35
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=lookup2_steps hc.lookup2Pre hc.lookup2Load hc.lookup2Post v pv
      (R-C) H (T (R-C)) hlt hH (hT _ hlt)
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
      (by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hbytes _ hlt)
    refine ⟨t,n+2+8,n+2+14,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt,eq_comm] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase2_steps
theorem phase3_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46966) (R C H : Nat) (hR : R≤63) (hC : C<2^64) (hH : H<5832)
    (h21 : s.getReg .x21=BitVec.ofNat 64 R) (h20 : s.getReg .x20=BitVec.ofNat 64 H)
    (hm : s.getMem (417872#64)=BitVec.ofNat 64 C) :
    ∃t n c,n≤11 ∧ c≤14 ∧ Steps im s n c t ∧
      t.pc=(if R-C<18 ∧ H/324=R-C then pcOf 46978 else pcOf 46979) ∧
      t.getReg .x21=BitVec.ofNat 64 (R-C) ∧ RegsExcept s t regs ∧ Frame s t (fun _=>False) := by
  letI:=hc.r2
  obtain ⟨u,n,hn,su,pu,u21,ru,fu⟩:=residual2_steps (im:=im) s hp R C hR hC h21 hm
  obtain ⟨v,sv,pv,rv,fv⟩:=range3_steps hc.range3 u pu (R-C) (by omega) u21
  by_cases hlt : R-C<18
  · rw [if_pos hlt] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=last_steps hc.last v pv (R-C) H (by omega) hH
      (by rw [rv.get (by decide)];exact u21)
      (by rw [rv.get (by decide),ru.get (by decide)];exact h20)
    refine ⟨t,n+2+3,n+2+6,by omega,by omega,(su.trans sv).trans st,?_,?_,?_,?_⟩
    · simpa [hlt] using pt
    · rw [rt.get (by decide),rv.get (by decide)];exact u21
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
  · rw [if_neg hlt] at pv
    refine ⟨v,n+2,n+2,by omega,by omega,su.trans sv,?_,?_,?_,?_⟩
    · simpa [hlt] using pv
    · rw [rv.get (by decide)];exact u21
    · exact (ru.trans rv).mono (by decide)
    · exact (fu.trans fv).mono (by simp)
#print axioms phase3_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedValidate
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 20000

abbrev Condition (H C0 C1 C2 : Nat) (T1 T2 : Nat→Nat) : Prop :=
  let R1:=63-C0
  let R2:=R1-C1
  let R3:=R2-C2
  R1<48 ∧ R2<35 ∧ R3<18 ∧ H%18=T1 R1 ∧ H/18%18=T2 R2 ∧ H/324=R3

theorem validate_steps {im : Image} (hc : Code im)
    (s : MachineState) (hp : s.pc=pcOf 46929) (H C0 C1 C2 : Nat)
    (hH : H<5832) (hC0 : C0<2^64) (hC1 : C1<2^64) (hC2 : C2<2^64)
    (hm : s.getMem (0x66000#64)=BitVec.ofNat 64 H)
    (hm0 : s.getMem (417856#64)=BitVec.ofNat 64 C0)
    (hm1 : s.getMem (417864#64)=BitVec.ofNat 64 C1)
    (hm2 : s.getMem (417872#64)=BitVec.ofNat 64 C2)
    (T1 T2 : Nat→Nat) (ht1 : ∀r,r<48→T1 r<18) (ht2 : ∀r,r<35→T2 r<18)
    (hb1 : ∀r,r<48→s.getByte (BitVec.ofNat 64 (16749456+r))=BitVec.ofNat 8 (T1 r))
    (hb2 : ∀r,r<35→s.getByte (BitVec.ofNat 64 (16749520+r))=BitVec.ofNat 8 (T2 r)) :
    ∃t n c,n≤47 ∧ c≤59 ∧ Steps im s n c t ∧
      t.pc=(if Condition H C0 C1 C2 T1 T2 then pcOf 42795 else pcOf 354) ∧
      RegsExcept s t [.x6,.x7,.x20,.x21,.x28,.x29] ∧ Frame s t (fun _=>False) := by
  obtain ⟨u,su,pu,u20,u21,ru,fu⟩:=init_steps hc.init s hp H hm
  obtain ⟨v,n1,c1,hn1,hc1,sv,pv,v21,rv,fv⟩:=phase1_steps hc u pu 63 C0 H (by omega) hC0 hH u21 u20
    (by rw [fu.get (by decide) (by simp)];exact hm0) T1 ht1
    (fun r hr=>by rw [fu.getByte (by omega) (by simp)];exact hb1 r hr)
  by_cases h1 : 63-C0<48 ∧ H%18=T1 (63-C0)
  · rw [if_pos h1] at pv
    obtain ⟨w,n2,c2,hn2,hc2,sw,pw,w21,rw_,fw⟩:=phase2_steps hc v pv (63-C0) C1 H (by omega) hC1 hH v21
      (by rw [rv.get (by decide)];exact u20)
      (by rw [fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm1) T2 ht2
      (fun r hr=>by rw [fv.getByte (by omega) (by simp),fu.getByte (by omega) (by simp)];exact hb2 r hr)
    by_cases h2 : 63-C0-C1<35 ∧ H/18%18=T2 (63-C0-C1)
    · rw [if_pos h2] at pw
      obtain ⟨x,n3,c3,hn3,hc3,sx,px,x21,rx,fx⟩:=phase3_steps hc w pw (63-C0-C1) C2 H (by omega) hC2 hH w21
        (by rw [rw_.get (by decide),rv.get (by decide)];exact u20)
        (by rw [fw.get (by decide) (by simp),fv.get (by decide) (by simp),fu.get (by decide) (by simp)];exact hm2)
      by_cases h3 : 63-C0-C1-C2<18 ∧ H/324=63-C0-C1-C2
      · rw [if_pos h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=good_steps hc.good x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : Condition H C0 C1 C2 T1 T2 := by exact ⟨h1.1,h2.1,h3.1,h1.2,h2.2,h3.2⟩
          simpa only [if_pos hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
      · rw [if_neg h3] at px
        obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad x px
        refine ⟨t,4+n1+n2+n3+1,4+c1+c2+c3+1,by omega,by omega,(((su.trans sv).trans sw).trans sx).trans st,?_,?_,?_⟩
        · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h3 ⟨h.2.2.1,h.2.2.2.2.2⟩
          simpa [hcond] using pt
        · exact ((((ru.trans rv).trans rw_).trans rx).trans rt).mono (by decide)
        · exact ((((fu.trans fv).trans fw).trans fx).trans ft).mono (by simp)
    · rw [if_neg h2] at pw
      obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad w pw
      refine ⟨t,4+n1+n2+1,4+c1+c2+1,by omega,by omega,((su.trans sv).trans sw).trans st,?_,?_,?_⟩
      · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h2 ⟨h.2.1,h.2.2.2.2.1⟩
        simpa [hcond] using pt
      · exact (((ru.trans rv).trans rw_).trans rt).mono (by decide)
      · exact (((fu.trans fv).trans fw).trans ft).mono (by simp)
  · rw [if_neg h1] at pv
    obtain ⟨t,st,pt,rt,ft⟩:=bad_steps hc.bad v pv
    refine ⟨t,4+n1+1,4+c1+1,by omega,by omega,(su.trans sv).trans st,?_,?_,?_⟩
    · have hcond : ¬Condition H C0 C1 C2 T1 T2 := by intro h;exact h1 ⟨h.1,h.2.2.2.1⟩
      simpa [hcond] using pt
    · exact ((ru.trans rv).trans rt).mono (by decide)
    · exact ((fu.trans fv).trans ft).mono (by simp)
#print axioms validate_steps
end ClaudeWCT.W9.Machine.Expand.SharedValidate

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def moveCode : List (BitVec 32) := [0xe3303,0x6eb023,0xff8e0e13,0xff8e8e93,0xfff90913,0xfe0916e3]
sym_block moveRun := symRun {noAlias:=true} moveCode (pcOf 46895) 20

theorem move_step {im : Image} (hc : CodeAt im (pcOf 46895) moveCode)
    (s : MachineState) (hp : s.pc=pcOf 46895) (X Y n : Nat)
    (hx8 : X%8=0) (hy8 : Y%8=0) (hx : 8≤X) (hy : 8≤Y)
    (hX : X≤35000) (hY : Y≤35000) (hn : 0<n) (hn' : n<2^64)
    (h28 : s.getReg .x28=BitVec.ofNat 64 X)
    (h29 : s.getReg .x29=BitVec.ofNat 64 Y)
    (h18 : s.getReg .x18=BitVec.ofNat 64 n) :
    ∃t,Steps im s 6 6 t ∧ t.pc=(if n=1 then pcOf 46901 else pcOf 46895) ∧
      t.getReg .x28=BitVec.ofNat 64 (X-8) ∧ t.getReg .x29=BitVec.ofNat 64 (Y-8) ∧
      t.getReg .x18=BitVec.ofNat 64 (n-1) ∧
      t.getMem (BitVec.ofNat 64 Y)=s.getMem (BitVec.ofNat 64 X) ∧
      RegsExcept s t [.x6,.x18,.x28,.x29] ∧ Frame s t (fun A=>A=Y) := by
  have hxsub : (BitVec.ofNat 64 X+18446744073709551608 : Word)=BitVec.ofNat 64 (X-8) := by
    exact ofNat_sub8 X hx (by omega)
  have hysub : (BitVec.ofNat 64 Y+18446744073709551608 : Word)=BitVec.ofNat 64 (Y-8) := by
    exact ofNat_sub8 Y hy (by omega)
  have hnsub : (BitVec.ofNat 64 n+18446744073709551615 : Word)=BitVec.ofNat 64 (n-1) := by
    conv_lhs => rw [show n=(n-1)+1 by omega,BitVec.ofNat_add,BitVec.add_assoc]
    change BitVec.ofNat 64 (n-1)+0=BitVec.ofNat 64 (n-1)
    exact BitVec.add_zero _
  refine ⟨_,symRun_sound moveRun hc s hp ?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [moveRun.res,rv_simp,h28,h29,accessValid_iff,MEMORY_BYTES]
    omega
  · simp only [Result.toState_pc,moveRun.res,E.eval,BinOp.eval,CmpOp.eval,h18,hnsub]
    have hz : (BitVec.ofNat 64 (n-1)=0) ↔ n=1 := by
      constructor
      · intro he;have he' := congrArg BitVec.toNat he
        change (n-1)%2^64=0 at he'
        rw [Nat.mod_eq_of_lt (show n-1<2^64 by omega)] at he'
        omega
      · rintro rfl;rfl
    change (if ((BitVec.ofNat 64 n+18446744073709551615 : Word) != 0) then pcOf 46895 else pcOf 46901) = _
    rw [hnsub]
    simp only [bne_iff_ne,ne_eq,hz]
    split_ifs <;> rfl
  · change s.getReg .x28+18446744073709551608=_
    rw [h28];exact hxsub
  · change s.getReg .x29+18446744073709551608=_
    rw [h29];exact hysub
  · change s.getReg .x18+18446744073709551615=_
    rw [h18];exact hnsub
  · simp only [Result.toState_getMem,moveRun.res]
    t3n [h28,h29]
    simp
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hnA
    simp only [Result.toState_getMem,moveRun.res]
    t3n [h28,h29]
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    simp only [Nat.add_zero,Nat.mod_eq_of_lt (show Y<18446744073709551616 by omega),if_neg hnA]

theorem move_loop {im : Image} (hc : CodeAt im (pcOf 46895) moveCode)
    (S D : Nat) (hs8 : S%8=0) (hd8 : D%8=0) (hs : 8≤S) (hsd : S<D) :
    ∀n (s : MachineState), D+8*n≤35000 → s.pc=pcOf 46895 →
      s.getReg .x28=BitVec.ofNat 64 (S+8*n) →
      s.getReg .x29=BitVec.ofNat 64 (D+8*n) →
      s.getReg .x18=BitVec.ofNat 64 (n+1) →
      ∃t,Steps im s (6*(n+1)) (6*(n+1)) t ∧ t.pc=pcOf 46901 ∧
        t.getReg .x28=BitVec.ofNat 64 (S-8) ∧ t.getReg .x29=BitVec.ofNat 64 (D-8) ∧
        t.getReg .x18=0 ∧
        (∀i≤n,t.getMem (BitVec.ofNat 64 (D+8*i))=s.getMem (BitVec.ofNat 64 (S+8*i))) ∧
        RegsExcept s t [.x6,.x18,.x28,.x29] ∧
        Frame s t (fun A=>D≤A ∧ A<D+8*(n+1)) := by
  intro n
  induction n with
  | zero =>
    intro s hb hp h28 h29 h18
    simp only [Nat.mul_zero,Nat.add_zero] at hb h28 h29
    obtain ⟨t,st,pt,r28,r29,r18,mt,rt,ft⟩:=move_step hc s hp S D 1 hs8 hd8 hs (by omega) (by omega) hb (by decide) (by decide) h28 h29 h18
    refine ⟨t,by simpa using st,by simpa using pt,r28,r29,by simpa using r18,?_,rt,ft.mono (by intro A hA h;omega)⟩
    intro i hi
    have : i=0 := by omega
    simpa [this] using mt
  | succ n ih =>
    intro s hb hp h28 h29 h18
    obtain ⟨u,su,pu,r28,r29,r18,mu,ru,fu⟩:=move_step hc s hp (S+8*(n+1)) (D+8*(n+1)) (n+2)
      (by omega) (by omega) (by omega) (by omega) (by omega) hb (by omega) (by omega) h28 h29 h18
    have p : u.pc=pcOf 46895 := by simpa using pu
    have a : u.getReg .x28=BitVec.ofNat 64 (S+8*n) := by rw [r28,show S+8*(n+1)-8=S+8*n by omega]
    have b : u.getReg .x29=BitVec.ofNat 64 (D+8*n) := by rw [r29,show D+8*(n+1)-8=D+8*n by omega]
    have c : u.getReg .x18=BitVec.ofNat 64 (n+1) := by simpa using r18
    obtain ⟨t,ut,pt,t28,t29,t18,mt,rt,ft⟩:=ih u (by omega) p a b c
    refine ⟨t,?_,pt,t28,t29,t18,?_,(ru.trans rt).mono (by decide),?_⟩
    · convert su.trans ut using 1 <;> omega
    · intro i hi
      by_cases hin : i≤n
      · rw [mt i hin,fu.get (by omega) (by omega)]
      · have he : i=n+1 := by omega
        subst i
        rw [ft.get (by omega) (by omega)];exact mu
    · exact (fu.trans ft).mono (by intro A hA h;rcases h with h|h <;> omega)
#print axioms move_step
#print axioms move_loop
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
def setupCode : List (BitVec 32) := [0x4c000e13,0x20eb7,0x260e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x30e3303,0x38e3383,0x26eb823,0x27ebc23,0x7e37,0xe0e13,0x1eb7,0x800e8e93,0xe3303,0x8e3383,0x6eb023,0x7eb423,0x66e37,0xe0e13,0x8e3303,0x6eb823,0xebc23,0x20eb023,0x20eb423,0x20eb823,0x20ebc23,0x8e37,0x4b8e0e13,0x8eb7,0x5e8e8e93,0x1ac00913]
sym_block setupRun := symRun {noAlias:=true} setupCode (pcOf 46862) 100
def tailCode : List (BitVec 32) := [0x22137,0x10113,0x293,0xf04d206f]
sym_block tailRun := symRun {noAlias:=true} tailCode (pcOf 46901) 20

theorem setup_steps {im : Image} (hc : CodeAt im (pcOf 46862) setupCode)
    (s : MachineState) (hp : s.pc=pcOf 46862) :
    ∃t,Steps im s 33 33 t ∧ t.pc=pcOf 46895 ∧
      t.getReg .x28=33976 ∧ t.getReg .x29=34280 ∧ t.getReg .x18=428 ∧
      (∀o,o=0 ∨ o=8 ∨ o=48 ∨ o=56 → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (1216+o))) ∧
      (∀i<2,t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i))) ∧
      t.getMem 2064=s.getMem 0x66008 ∧
      (∀ i : Nat, 3 ≤ i → i < 8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0) ∧
      RegsExcept s t [.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112)) := by
  refine ⟨_,symRun_sound setupRun hc s hp ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [setupRun.res,rv_simp,accessValid_iff,MEMORY_BYTES]
  · rfl
  · rfl
  · rfl
  · rfl
  · intro o ho
    rcases ho with rfl|rfl|rfl|rfl <;> simp [setupRun.res,rv_simp]
  · intro i hi
    interval_cases i <;> simp [setupRun.res,rv_simp]
  · simp [setupRun.res,rv_simp]
  · intro i hlo hhi
    interval_cases i <;> simp [setupRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn
    simp only [Result.toState_getMem,setupRun.res]
    t3n []
    rw [Nat.mod_eq_of_lt (show A<18446744073709551616 by simpa using hA)]
    split_ifs <;> first | rfl | omega

theorem tail_steps {im : Image} (hc : CodeAt im (pcOf 46901) tailCode)
    (s : MachineState) (hp : s.pc=pcOf 46901) :
    ∃t,Steps im s 4 4 t ∧ t.pc=pcOf 249 ∧ t.getReg .x2=0x22000 ∧
      t.getReg .x5=0 ∧ RegsExcept s t [.x2,.x5] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound tailRun hc s hp ?_,rfl,rfl,rfl,?_,?_⟩
  · simp [tailRun.res,rv_simp]
  · intro r hr
    cases r <;> first | exact (hr (by decide)).elim | rfl
  · intro A hA hn;rfl
#print axioms setup_steps
#print axioms tail_steps
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
structure Code (im : Image) : Prop where
  setup : CodeAt im (pcOf 46862) setupCode
  move : CodeAt im (pcOf 46895) moveCode
  tail : CodeAt im (pcOf 46901) tailCode

theorem steps {im : Image} (hc : Code im) (s : MachineState) (hp : s.pc=pcOf 46862) :
    ∃t,Steps im s 2605 2605 t ∧ t.pc=pcOf 249 ∧ t.getReg .x2=0x22000 ∧ t.getReg .x5=0 ∧
      (∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (1216+o))) ∧
      (∀i,i<2 → t.getMem (BitVec.ofNat 64 (2048+8*i))=s.getMem (BitVec.ofNat 64 (0x7000+8*i))) ∧
      t.getMem 2064=s.getMem 0x66008 ∧
      (∀ i : Nat, 3 ≤ i → i < 8 → t.getMem (BitVec.ofNat 64 (2048+8*i))=0) ∧
      (∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i))) ∧
      RegsExcept s t [.x2,.x5,.x6,.x7,.x18,.x28,.x29] ∧
      Frame s t (fun A=>A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112) ∨ (30864≤A ∧ A<34288)) := by
  obtain ⟨u,su,pu,u28,u29,u18,roots,rho,dc,z,ru,fu⟩:=setup_steps hc.setup s hp
  obtain ⟨v,uv,pv,v28,v29,v18,mv,rv,fv⟩:=move_loop hc.move 30560 30864 (by decide) (by decide) (by decide) (by decide)
    427 u (by decide) pu u28 u29 u18
  obtain ⟨t,vt,pt,t2,t5,rt,ft⟩:=tail_steps hc.tail v pv
  have gm : ∀A,A<2^64 → ¬(30864≤A ∧ A<34288) → t.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A) := by
    intro A hA hn
    rw [ft.get hA (by simp),fv.get hA (by simpa using hn)]
  refine ⟨t,by convert su.trans (uv.trans vt) using 1 <;> norm_num,pt,t2,t5,?_,?_,?_,?_,?_,?_,?_⟩
  · intro o ho
    rw [gm _ (by rcases ho with rfl|rfl|rfl|rfl <;> decide) (by rcases ho with rfl|rfl|rfl|rfl <;> decide)]
    exact roots o ho
  · intro i hi
    rw [gm _ (by omega) (by omega)];exact rho i hi
  · rw [show (2064:Word)=BitVec.ofNat 64 2064 by rfl,gm _ (by decide) (by decide)];exact dc
  · intro i hi hi'
    rw [gm _ (by omega) (by omega)];exact z i hi hi'
  · intro i hi
    rw [ft.get (by omega) (by simp),mv i (by omega),fu.get (by omega) (by omega)]
  · exact ((ru.trans rv).trans rt).mono (by decide)
  · exact ((fu.trans fv).trans ft).mono (by intro A hA h;rcases h with (h|h)|h <;> first | tauto | omega)
#print axioms steps
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedZero
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem clear_witness {im : Image} (p : Word) (hc : CodeAt im p words)
    (s : MachineState) (hp : s.pc=p) (h28 : s.getReg .x28=1216) (h29 : s.getReg .x29=9472) :
    ∃t,Steps im s 3096 3096 t ∧ t.pc=p+12 ∧
      (∀A,A%8=0 → 1216≤A → A<9472 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun A=>1216≤A ∧ A<9472) := by
  obtain ⟨t,st,pt,r28,mt,rt,ft⟩:=loop p hc 1216 (by decide) 1031 s (by decide) hp h28 h29
  refine ⟨t,st,pt,?_,rt,ft⟩
  intro A ha hlo hhi
  have he : 1216+8*((A-1216)/8)=A := by omega
  rw [←he];exact mt _ (by omega)

structure ClearCode (im : Image) : Prop where
  accepted : CodeAt im (pcOf 45232) acceptedCode
  firstZero : CodeAt im (pcOf 45254) words
  finalScatter : CodeAt im (pcOf 46980) finalScatterCode
  finalZero : CodeAt im (pcOf 47001) words
  back : CodeAt im (pcOf 47004) [0xcb4fe06f]

theorem accepted_clear {im : Image} (hc : ClearCode im)
    (s : MachineState) (hp : s.pc=pcOf 45232) (h17 : s.getReg .x17=0x20160) :
    ∃t,Steps im s 3118 3118 t ∧ t.pc=pcOf 45257 ∧
      (∀A,A%8=0 → 1216≤A → A<9472 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      t.getMem 0x66020=0 ∧ t.getMem 0x66008=s.getReg .x19 ∧
      t.getMem 0x66010=s.getMem 0x20160 >>> 33 ∧
      t.getMem 0x20550=s.getMem 0x20160 >>> 33 ∧
      (∀i,i<4 → t.getMem (BitVec.ofNat 64 (96+8*i))=s.getMem (BitVec.ofNat 64 (0x20160+8*i))) ∧
      RegsExcept s t [.x6,.x22,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66020 ∨ A=0x66008 ∨ A=0x66010 ∨ A=0x20550 ∨ (96≤A ∧ A<128) ∨ (1216≤A ∧ A<9472)) := by
  obtain ⟨u,su,pu,u28,u29,mode,ctr,index,idx,digest,ru,fu⟩:=accepted_steps hc.accepted s hp h17
  obtain ⟨t,ut,pt,zeros,rt,ft⟩:=clear_witness (pcOf 45254) hc.firstZero u pu u28 u29
  refine ⟨t,by convert su.trans ut using 1,pt,zeros,?_,?_,?_,?_,?_,(ru.trans rt).mono (by decide),?_⟩
  · exact (ft.get (by decide) (by decide)).trans mode
  · exact (ft.get (by decide) (by decide)).trans ctr
  · exact (ft.get (by decide) (by decide)).trans index
  · exact (ft.get (by decide) (by decide)).trans idx
  · intro i hi;rw [ft.get (by omega) (by omega)];exact digest i hi
  · exact (fu.trans ft).mono (by intro A hA h;tauto)

theorem final_clear {im : Image} (hc : ClearCode im)
    (s : MachineState) (hp : s.pc=pcOf 46980) :
    ∃t,Steps im s 3118 3118 t ∧ t.pc=pcOf 45257 ∧
      (∀A,A%8=0 → 1216≤A → A<9472 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      t.getMem 0x66018=s.getMem 1248 ∧ t.getMem 0x66020=1 ∧
      (∀i,i<4 → t.getMem (BitVec.ofNat 64 (0x20160+8*i))=s.getMem (BitVec.ofNat 64 (96+8*i))) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧
      Frame s t (fun A=>A=0x66018 ∨ A=0x66020 ∨ (0x20160≤A ∧ A<0x20180) ∨ (1216≤A ∧ A<9472)) := by
  obtain ⟨u,su,pu,u28,u29,ctr,mode,digest,ru,fu⟩:=finalScatter_steps hc.finalScatter s hp
  obtain ⟨v,uv,pv,zeros,rv,fv⟩:=clear_witness (pcOf 47001) hc.finalZero u pu u28 u29
  have jump : Steps im v 1 1 (v.setPC (pcOf 45257)) := by
    obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0xcb4fe06f#32) 47004=some 45257 by decide)
    exact jal_x0_step hc.back hd ho v pv
  refine ⟨v.setPC (pcOf 45257),by convert su.trans (uv.trans jump) using 1,rfl,zeros,?_,?_,?_,(ru.trans rv).mono (by decide),?_⟩
  · exact (fv.get (by decide) (by decide)).trans ctr
  · exact (fv.get (by decide) (by decide)).trans mode
  · intro i hi;exact (fv.get (by omega) (by omega)).trans (digest i hi)
  · exact (fu.trans fv).mono (by intro A hA h;tauto)
#print axioms clear_witness
#print axioms accepted_clear
#print axioms final_clear
end ClaudeWCT.W9.Machine.Expand.SharedZero

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem SharedHandoff.code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : SharedHandoff.Code im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=1806) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1839) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1845) hc (by decide +kernel) (by decide +kernel)
theorem SharedHandoff.installed_code : SharedHandoff.Code Images.expandImage := SharedHandoff.code_of_driver codeAt_expand_shared_driver

theorem SharedZero.code_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : SharedZero.ClearCode im := by
  constructor
  · exact SharedCounterHooks.code_slice (off:=176) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=198) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1924) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1945) hc (by decide +kernel) (by decide +kernel)
  · exact SharedCounterHooks.code_slice (off:=1948) hc (by decide +kernel) (by decide +kernel)
theorem SharedZero.installed_code : SharedZero.ClearCode Images.expandImage := SharedZero.code_of_driver codeAt_expand_shared_driver

theorem SharedScatter.after_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 46509) SharedScatter.afterCode := by
  exact SharedCounterHooks.code_slice (off:=1453) hc (by decide +kernel) (by decide +kernel)
theorem SharedScatter.finish_of_driver {im : Image}
    (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 47005) SharedScatter.finishCode := by
  exact SharedCounterHooks.code_slice (off:=1949) hc (by decide +kernel) (by decide +kernel)
theorem SharedScatter.installed_after : CodeAt Images.expandImage (pcOf 46509) SharedScatter.afterCode := SharedScatter.after_of_driver codeAt_expand_shared_driver
theorem SharedScatter.installed_finish : CodeAt Images.expandImage (pcOf 47005) SharedScatter.finishCode := SharedScatter.finish_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
theorem expand_steps {im : Image} (hc : CodeAt im (pcOf 45226) expandCode)
    (s : MachineState) (hp : s.pc=pcOf 45226) :
    Steps im s 1 1 (s.setPC (pcOf 45232)) := by
  exact ClaudeWCT.W9.Machine.Expand.jal_x0_step (imm:=24) hc (by rfl) (by decide) s hp

end ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M W9Machine
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def rawSlots (k child : Nat) (values : Fin 6→SigGolfCandidate.T3.Digest)
    (path : Nat→SigGolfCandidate.T3.Digest) : List (Nat×SigGolfCandidate.T3.Digest) :=
  ((List.finRange 6).flatMap fun i=>[(V3.chainOffset k i.val+48,values i),
    (V3.regionOffset k+V3.leafSlot i.val,values i)]) ++
  ((List.range (SharedV3.lastLevel k+1)).map fun l=>(V3.regionOffset k+SharedV3.sibOff child l,path l)) ++
  [(SharedV3.topOtherOff k child,path (SharedV3.lastLevel k+1))]

theorem rawSlots_written (k : Fin 9) (child : Fin 128)
    (values : Fin 6→SigGolfCandidate.T3.Digest) (path : Nat→SigGolfCandidate.T3.Digest)
    (p : Nat×SigGolfCandidate.T3.Digest) (hp:p∈rawSlots k.val child.val values path)
    (half : Nat) (hh:half<2) : PreciseCoordinateW k.val child.val (1216+p.1+8*half) := by
  unfold rawSlots at hp
  simp only [List.mem_append,List.mem_flatMap,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with (⟨i,hi,hp⟩|⟨l,hl,hp⟩)|hp
  · rcases hp with rfl|rfl
    · rw [←chainDestination_source k i]
      apply Or.inl;apply Or.inl;apply Or.inl
      refine ⟨i.val,i.isLt,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
    · by_cases hz:i.val=0
      · have ie:i=0:=Fin.ext hz
        subst i
        change PreciseCoordinateW k.val child.val (1216+(V3.regionOffset k.val+688)+8*half)
        rw [show V3.regionOffset k.val+688=V3.chainOffset k.val 0+48 by unfold V3.chainOffset;omega,
          show 1216+(V3.chainOffset k.val 0+48)=coordRegion k.val+688 by
            simpa only [Fin.val_zero] using (chainDestination_source k (0:Fin 6)).symm]
        apply Or.inl;apply Or.inl;apply Or.inl
        refine ⟨0,by decide,?_⟩
        interval_cases half
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl (by omega))
      · rw [←leafDestination_source k i (by omega)]
        apply Or.inl;apply Or.inl;apply Or.inl
        refine ⟨i.val,i.isLt,Or.inr (Or.inr ⟨by omega,?_⟩)⟩
        interval_cases half
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
  · subst p
    have hlt:l<SharedV3.lastLevel k.val+1:=List.mem_range.mp hl
    by_cases h5:l<5
    · rw [←Nat.add_assoc,←pathDestination_source k child ⟨l,h5⟩]
      simp only [Fin.val_mk]
      apply Or.inl;apply Or.inl;apply Or.inr
      refine ⟨l,h5,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    · have hn:¬firstCoord k.val:=by
        intro h
        have hf:SharedV3.first k.val=true:=by simpa [SharedV3.first,firstCoord] using h
        simp [SharedV3.lastLevel,hf] at hlt
        omega
      have hl5:l=5:=by unfold SharedV3.lastLevel at hlt;split at hlt <;> omega
      subst l
      rw [←Nat.add_assoc,←sixthDestination_source k child]
      apply Or.inl;apply Or.inr
      refine ⟨hn,?_⟩
      interval_cases half
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · subst p
    rw [←topDest_source k child]
    interval_cases half
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

theorem slot_free_of_not_written (slots : List (Nat×SigGolfCandidate.T3.Digest))
    (W : Nat→Prop) (off : Nat) (ha:off%8=0)
    (halign:∀p∈slots,p.1%16=0)
    (hw:∀p∈slots,∀h,h<2→W (1216+p.1+8*h))
    (hn:¬W (1216+off)) : ∀p∈slots,off+8≤p.1 ∨ p.1+16≤off := by
  intro p hp
  have hal:=halign p hp
  by_contra h
  have he:off=p.1 ∨ off=p.1+8:=by omega
  rcases he with he|he
  · apply hn
    have hh:=hw p hp 0 (by decide)
    simpa [he] using hh
  · apply hn
    have hh:=hw p hp 1 (by decide)
    simpa [he,Nat.add_assoc] using hh
#print axioms rawSlots_written
#print axioms slot_free_of_not_written
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedDigestCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open Sign.SharedDigestBoundary
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
theorem success_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 45226) expandCode := by
  exact SharedCounterHooks.code_slice (off:=170) hc (by decide +kernel) (by decide +kernel)
theorem failure_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (failPC true) failureCode := by
  exact SharedCounterHooks.code_slice (off:=173) hc (by decide +kernel) (by decide +kernel)
theorem failure_ecall_of_driver {im : Image} (hc : CodeAt im (pcOf 45056) Images.expandSharedDriver) : CodeAt im (pcOf 45231) [0x73] := by
  exact SharedCounterHooks.code_slice (off:=175) hc (by decide +kernel) (by decide +kernel)
theorem installed_success : CodeAt Images.expandImage (pcOf 45226) expandCode := success_of_driver codeAt_expand_shared_driver
theorem installed_failure : CodeAt Images.expandImage (failPC true) failureCode := failure_of_driver codeAt_expand_shared_driver
theorem installed_failure_ecall : CodeAt Images.expandImage (pcOf 45231) [0x73] := failure_ecall_of_driver codeAt_expand_shared_driver
end ClaudeWCT.W9.Machine.Expand.SharedDigestCode

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e extractByte_bytesToWordLE_e)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def DB : Nat := 16747408

theorem getMem {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (A : Nat) (hA:A<2^64) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      if 0x7000≤A ∧ A<0x7000+5248 ∧ (A-0x7000)%8=0 then bytesToWordLE ((bytes b).drop (A-0x7000) |>.take 8)
      else if 0xA0≤A ∧ A<0xB0 ∧ (A-0xA0)%8=0 then bytesToWordLE ((bytes pk).drop (A-0xA0) |>.take 8)
      else if 0x65E0≤A ∧ A<0x6600 ∧ (A-0x65E0)%8=0 then bytesToWordLE ((bytes m).drop (A-0x65E0) |>.take 8)
      else if DB≤A ∧ A<DB+29808 ∧ (A-DB)%8=0 then bytesToWordLE (im.data.drop (A-DB) |>.take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg,getMem_writeBytesAsWords _ _ 0x7000 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw[bytes_length_e];decide) hA,
    getMem_writeBytesAsWords _ _ 0x65E0 A (by rw[bytes_length_e];decide) hA,hb,
    getMem_writeBytesAsWords _ _ DB A (by rw[hlen];decide) hA,
    bytes_length_e,bytes_length_e,bytes_length_e,hlen]
  rfl

theorem dataByte {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<29808) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (DB+i))=im.data.getD i 0 := by
  rw [getByte_eq_word _ _ (by unfold DB;omega),getMem hlen hb _ _ _ _ (by unfold DB;omega),
    if_neg (by unfold DB;omega),if_neg (by unfold DB;omega),if_neg (by unfold DB;omega),
    if_pos (by unfold DB;omega),extractByte_bytesToWordLE_e _ _ (Nat.mod_lt _ (by decide))]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_take,List.getElem?_drop,
    if_pos (Nat.mod_lt (DB+i) (show 0<8 by decide))]
  congr 2
  unfold DB
  omega

theorem signatureWord {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<656) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x7000+8*i))=b.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_pos (by omega),
    show 0x7000+8*i-0x7000=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e b i (by omega)

#print axioms getMem
#print axioms dataByte
#print axioms signatureWord
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Sign.SharedDigest
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

def DataAt (s : MachineState) : Prop := ∀i,i<2160 → s.getByte (BitVec.ofNat 64 (DB+i))=Images.expandSharedData.getD i 0

theorem ranks_data (f : Fin 563) : Images.expandSharedData.getD f.val 0=BitVec.ofNat 8 (rankByte f.val) := by
  have h:∀f:Fin 563,Images.expandSharedData.getD f.val 0=BitVec.ofNat 8 (rankByte f.val):=by decide +kernel
  exact h f

theorem correction_data (k : Fin 9) (j : Fin 32) : Images.expandSharedData.getD (correctionOffset true k.val+j.val) 0=BitVec.ofNat 8 (correctionByte k.val j.val) := by
  have h:∀k:Fin 9,∀j:Fin 32,Images.expandSharedData.getD (correctionOffset true k.val+j.val) 0=BitVec.ofNat 8 (correctionByte k.val j.val):=by decide +kernel
  exact h k j

theorem DataAt.tables {s : MachineState} (h:DataAt s) : TablesAt true s := by
  constructor
  · intro f hf
    rw [show tableBase true=DB by rfl,h f (by omega)]
    exact ranks_data ⟨f,hf⟩
  · intro k hk j hj
    have hb:correctionOffset true k≤1568:=by
      simp only [correctionOffset,↓reduceIte];split <;> omega
    rw [show tableBase true=DB by rfl,Nat.add_assoc,h _ (by omega)]
    exact correction_data ⟨k,hk⟩ ⟨j,hj⟩

#print axioms ranks_data
#print axioms correction_data
#print axioms DataAt.tables
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
theorem tail_steps {im : Image} (hc : CodeAt im (pcOf 1) frontTail) (s : MachineState)
    (hpc : s.pc = pcOf 1) (hx5 : s.getReg .x5 = 0) :
    ∃ t, Steps im s 29 29 t ∧ t.pc = pcOf 42719 ∧ t.getReg .x5 = 0 ∧
      t.getMem (BitVec.ofNat 64 0x800) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 0x808) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 DIG) = s.getMem (BitVec.ofNat 64 0x7000) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 8)) = s.getMem (BitVec.ofNat 64 0x7008) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x65E0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x65E8) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x65F0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x65F8) ∧
      RegsExcept s t [.x5, .x6, .x7, .x19, .x29, .x30] ∧
      Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) := by
  refine ⟨_, symRun_sound h2_front hc s hpc
    (by simp [h2_front.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, h2_front.res, E.eval]
  · simp [h2_front.res, rv_simp, hx5]
  iterate 8
    · simp only [Result.toState_getMem, h2_front.res, DIG]
      t3n []
  · ex_regs h2_front.res
  · intro A hA hn
    simp only [DIG] at hn
    simp only [Result.toState_getMem, h2_front.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]

#print axioms tail_steps
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.Machine.Expand
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Writes (A : Nat) : Prop := A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
  A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x59B0 ∨ A = 0x59B8 ∨ A = 0x59C0 ∨ A = 0x59C8

theorem setup {im : Image} (hf:CodeAt im (pcOf 1) frontTail) (hz:CodeAt im (pcOf 42719) zeroBlk)
    (hj:CodeAt im (pcOf 30) [0x7892b06f]) (s : MachineState) (hp:s.pc=pcOf 1) (hx5:s.getReg .x5=0) :
    ∃t,Steps im s 37 37 t ∧ t.pc=pcOf 45056 ∧ t.getReg .x5=0 ∧
      (∀A, A=0x800 ∨ A=DIG → t.getMem (BitVec.ofNat 64 A)=s.getMem 0x7000) ∧
      (∀A, A=0x808 ∨ A=DIG+8 → t.getMem (BitVec.ofNat 64 A)=s.getMem 0x7008) ∧
      (∀k,k<4 → t.getMem (BitVec.ofNat 64 (DIG+32+8*k))=s.getMem (BitVec.ofNat 64 (0x65E0+8*k))) ∧
      (∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → t.getMem (BitVec.ofNat 64 A)=0) ∧
      RegsExcept s t [.x5,.x6,.x7,.x19,.x29,.x30] ∧ Frame s t Writes := by
  obtain ⟨u,su,up,u5,a0,a8,d0,d8,d32,d40,d48,d56,ru,fu⟩:=tail_steps hf s hp hx5
  obtain ⟨v,uv,vp,v19,z,rv,fv⟩:=zero_spec hz u up
  have jump : Steps im v 1 1 (v.setPC (pcOf 45056)) := by
    obtain ⟨imm,hd,hoff⟩:=jalTo_sound (show jalTo (0x7892b06f#32) 30=some 45056 by decide)
    exact jal_x0_step hj hd hoff v vp
  have g:∀A,A<2^64 → ¬(A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8) → v.getMem (BitVec.ofNat 64 A)=u.getMem (BitVec.ofNat 64 A):=fv
  refine ⟨v.setPC (pcOf 45056),su.trans (uv.trans jump),rfl,?_,?_,?_,?_,?_,?_,?_⟩
  · rw[MachineState.getReg_setPC,rv.get (by decide),u5]
  · intro A h;rcases h with rfl|rfl
    · exact (g _ (by decide) (by simp[DIG])).trans a0
    · exact (g _ (by decide) (by simp[DIG])).trans d0
  · intro A h;rcases h with rfl|rfl
    · exact (g _ (by decide) (by simp[DIG])).trans a8
    · exact (g _ (by decide) (by simp[DIG])).trans d8
  · intro k hk
    rw[MachineState.getMem_setPC,g _ (by unfold DIG;omega) (by unfold DIG;omega)]
    interval_cases k
    · exact d32
    · exact d40
    · exact d48
    · exact d56
  · intro A h;exact z A (by rcases h with rfl|rfl|rfl|rfl <;> decide) h
  · exact (ru.trans rv).mono (by simp)
  · exact (fu.trans fv).mono (by intro A hA h;unfold Writes;rcases h with h|h <;> rcases h with h|h|h|h|h|h|h|h <;> omega)

#print axioms setup
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Expand (bytes_length_e extractByte_bytesToWordLE_e)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem prefixData {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (pref tail : List (BitVec 8)) (hp:pref.length=2160) (hd:im.data=pref++tail)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∀i,i<2160 → (w9init im m pk b).getByte (BitVec.ofNat 64 (DB+i))=pref.getD i 0 := by
  intro i hi
  rw [dataByte hlen hb m pk b i (by omega),hd]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append,hp,if_pos hi]

theorem msgWord {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi:i<4) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 (0x65E0+8*i))=m.extractLsb' (64*i) 64 := by
  rw [getMem hlen hb _ _ _ _ (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),
    show 0x65E0+8*i-0x65E0=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e m i (by omega)

theorem zero {im : Image} (hlen:im.data.length=29808) (hb:dataBase im=DB)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (A : Nat) (hA:A<DB)
    (hs:A<0x7000 ∨ 0x7000+5248≤A) (hp:A<0xA0 ∨ 0xB0≤A)
    (hm:A<0x65E0 ∨ 0x6600≤A) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  rw[getMem hlen hb _ _ _ _ (by unfold DB at hA;omega),
    if_neg (by omega),if_neg (by omega),if_neg (by omega),if_neg (by omega)]

#print axioms prefixData
#print axioms msgWord
#print axioms zero
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem invalid_front {im : Image} (he:CodeAt im (pcOf 0) [entryWord])
    (ht:CodeAt im (pcOf 44096) tailWords) (hg:CodeAt im (pcOf 44106) guardWords)
    (hj:CodeAt im (pcOf 44192) [0xb08d506f]) (s : MachineState) (hp:s.pc=pcOf 0)
    (H : Nat) (hlo:5832≤H) (hhi:H<65536) (hh:s.getMem 0x8478 >>> 48=BitVec.ofNat 64 H) :
    ∃t,Steps im s 15 15 t ∧ t.pc=pcOf 354 ∧
      RegsExcept s t [.x6,.x7,.x15,.x28,.x29,.x30] ∧ Frame s t (fun A=>A=policyAddress) := by
  obtain ⟨u,su,up,u6,u7,u28,um,ru,fu⟩:=tail_full ht (s.setPC (pcOf 44096)) rfl
  obtain ⟨v,uv,vp,rv,fv⟩:=guard_spec hg u up H hhi (u28.trans hh)
  rw[if_neg (by omega)] at vp
  have jump:Steps im v 1 1 (v.setPC (pcOf 354)) := by
    obtain ⟨imm,hd,hoff⟩:=jalTo_sound (show jalTo (0xb08d506f#32) 44192=some 354 by decide)
    exact jal_x0_step hj hd hoff v vp
  refine ⟨v.setPC (pcOf 354),(entry_step he s hp).trans (su.trans (uv.trans jump)),rfl,?_,?_⟩
  · exact (ru.trans rv).mono (by simp)
  · exact (fu.trans fv).mono (by intro A hA h;exact h.elim id False.elim)

#print axioms invalid_front
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_tail : CodeAt Images.expandImage (pcOf 1) frontTail := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_zero : CodeAt Images.expandImage (pcOf 42719) zeroBlk := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_jump : CodeAt Images.expandImage (pcOf 30) [0x7892b06f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_invalid : CodeAt Images.expandImage (pcOf 44192) [0xb08d506f] := by
  apply codeAt_expand_current_chunk <;> decide +kernel
#print axioms installed_tail
#print axioms installed_zero
#print axioms installed_jump
#print axioms installed_invalid
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem dataBase_of_length {im:Image} (h:im.data.length=29808) : dataBase im=DB := by
  unfold dataBase
  rw[h]
  rfl

theorem installed_dataBase : dataBase Images.expandImage=DB :=
  dataBase_of_length Images.expandData_length

theorem initial_data (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    DataAt (w9init Images.expandImage m pk b) := by
  exact prefixData Images.expandData_length installed_dataBase Images.expandSharedData
    (Images.expandPrefixData++Images.expandLegacyData) Images.expandSharedData_length
    (by change Images.expandData=Images.expandSharedData++(Images.expandPrefixData++Images.expandLegacyData)
        simp only[Images.expandData,List.append_assoc]) m pk b

#print axioms installed_dataBase
#print axioms initial_data
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def InflatedAt (s : MachineState) (b : SharedCodec.CBytes) : Prop :=
  ∀k,k<332 → DigAt s (0x7000+16*k)
    (SharedCodec.inflatedRead (0:Digest) (SharedCodec.digC b) k)

theorem InflatedAt.value {s : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    (k : Fin 9) (i : Fin 6) :
    DigAt s (SharedScatter.coordSource k.val+16*i.val)
      (Paired.coordinateValues (SharedCodec.sigDecC b).forest k i) := by
  have hh:=h (1+13*k.val+i.val) (by have:=k.isLt;have:=i.isLt;omega)
  rw [inflated_coordinate_value] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega

theorem InflatedAt.path {s : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    (k : Fin 9) (level : Nat) (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    DigAt s (SharedScatter.coordSource k.val+96+16*level)
      (Paired.coordinatePath (SharedCodec.sigDecC b).forest k level) := by
  have hb:level<7:=by split_ifs at hl <;> omega
  have hh:=h (1+13*k.val+6+level) (by have:=k.isLt;omega)
  rw [inflated_coordinate_path b k level hl] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega
#print axioms InflatedAt.value
#print axioms InflatedAt.path
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem sourceReadout_of_fields (w : W9Machine.WBytes) (s : MachineState) (k : Fin 9)
    (child : Fin 128) (values : Fin 6→Digest) (path : Nat→Digest)
    (hv : ∀i:Fin 6,DigAt s (coordSource k.val+16*i.val) (values i))
    (hp : ∀l,l<SharedV3.lastLevel k.val+2 → DigAt s (coordSource k.val+96+16*l) (path l))
    (hc : ∀i:Fin 6,wdig w (V3.chainOffset k.val i.val+48)=values i)
    (he : ∀i:Fin 6,wdig w (V3.regionOffset k.val+V3.leafSlot i.val)=values i)
    (hs : ∀l,l<SharedV3.lastLevel k.val+1 → wdig w (V3.regionOffset k.val+SharedV3.sibOff child.val l)=path l)
    (ht : wdig w (SharedV3.topOtherOff k.val child.val)=path (SharedV3.lastLevel k.val+1)) :
    SourceReadout w s k.val child.val := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi; rw[hc ⟨i,hi⟩];exact hv ⟨i,hi⟩
  · intro i hi hip;rw[he ⟨i,hi⟩];exact hv ⟨i,hi⟩
  · intro l hl
    have hb:l<SharedV3.lastLevel k.val+1:=by unfold SharedV3.lastLevel;split_ifs <;> omega
    rw[hs l hb];exact hp l (by omega)
  · intro hn
    have hf:SharedV3.first k.val=false:=by simpa[SharedV3.first,firstCoord] using hn
    have hl:SharedV3.lastLevel k.val=5:=by simp[SharedV3.lastLevel,hf]
    rw[hs 5 (by omega)]
    simpa using hp 5 (by omega)
  · rw[ht,topInput_source k]
    simpa only [Nat.add_assoc] using hp (SharedV3.lastLevel k.val+1) (by omega)
#print axioms sourceReadout_of_fields
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.T3M Paired W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem canonical_sourceReadout (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s : MachineState) (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest) (k : Fin 9) :
    SourceReadout (witEnc output witness) s k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) := by
  let child : Fin 128 := ⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
    coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
  have hc:child.val=SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val:=coordPhysical_source _ _
  rw[←hc]
  apply sourceReadout_of_fields (witEnc output witness) s k child
    (coordinateValues witness.signature.forest k) (coordinatePath witness.signature.forest k)
  · intro i;rw[hforest];exact hin.value k i
  · intro l hl
    rw[hforest]
    apply hin.path k l
    simp only [SharedV3.lastLevel,SharedV3.first,decide_eq_true_eq] at hl
    split_ifs at hl ⊢ with h <;> simp_all
  · exact wchainValue_witEnc output witness k
  · exact wleafValue_witEnc output witness k
  · intro l hl
    rw[hc]
    exact wsibling_witEnc output witness k l hl
  · rw[hc]
    exact wtopOther_witEnc output witness k
#print axioms canonical_sourceReadout
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Research.SharedPathPacking
open ClaudeWCT.W9.Machine.Expand.SharedScatter
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

theorem plans_data (child : Fin 128) (j : Fin 5) :
    Images.expandSharedData.getD (1024+5*(child.val%32)+j.val) 0=
      BitVec.ofNat 8 (packedSlots child.val j.val) := by
  have h:∀child:Fin 128,∀j:Fin 5,
      Images.expandSharedData.getD (1024+5*(child.val%32)+j.val) 0=
      BitVec.ofNat 8 (packedSlots child.val j.val):=by decide +kernel
  exact h child j

theorem DataAt.plans {s : MachineState} (h:DataAt s) : SharedScatter.PlanAt s := by
  intro child j hj
  have hm:=Nat.mod_lt child.val (by decide:0<32)
  rw [show 16748432+5*(child.val%32)+j=DB+(1024+5*(child.val%32)+j) by unfold DB;omega,
    h _ (by omega)]
  exact plans_data child ⟨j,hj⟩
#print axioms plans_data
#print axioms DataAt.plans
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ScatterInv.original_prefix (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s t : MachineState)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hi : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hz : ∀ (off : Nat), off + 8 ≤ 8256 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (1216+off))=0)
    (off : Nat) (hb : off+8≤8256) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) :
    W9Machine.OrigW (Paired.witEnc output witness) t (1216+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply PairedReadout.original_prefix_of_slots output witness s t writes _ _ _ hz off hb ha hc
  · intro p hp half hh
    obtain ⟨k,hk,hp⟩:=List.mem_flatMap.mp hp
    refine ⟨k,k.isLt,?_⟩
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply rawSlots_written k child (Paired.coordinateValues witness.signature.forest k)
      (Paired.coordinatePath witness.signature.forest k) p _ half hh
    simpa only [Paired.coordinateSlots,rawSlots,child,coordPhysical_source] using hp
  · intro A hA
    obtain ⟨k,hk,hw⟩:=hA
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply CoordinateReadout.original k child (hi.readout k hk) _ A hw
    simpa only [child,coordPhysical_source] using canonical_sourceReadout output witness b s hin hforest k
  · intro A hA hn
    exact hi.exactFrame.get hA hn
#print axioms ScatterInv.original_prefix
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem serializedWord_congr (r q : Nat→BitVec 64) (k : Nat) (hk:k<664)
    (h : ∀ j, j < 656 → r j = q j) : serializedWord r k=serializedWord q k := by
  unfold serializedWord
  split_ifs <;> first | rfl | rw[h _ (by omega)]

theorem hints_word (b : SharedCodec.CBytes) :
    b.extractLsb' (64*655) 64 >>> 48 = (b.extractLsb' (8*5246) 16).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_ushiftRight,BitVec.getLsbD_extractLsb',BitVec.getLsbD_setWidth,
    hj,decide_true,Bool.true_and]
  by_cases h:j<16
  · rw[show decide (48+j<64)=true from decide_eq_true (by omega),
      show decide (j<16)=true from decide_eq_true h]
    simp only [Bool.true_and]
    congr 1
    omega
  · rw[show decide (48+j<64)=false from decide_eq_false (by omega),
      show decide (j<16)=false from decide_eq_false h]
    simp

theorem serializedWord_eq (read : Nat→BitVec 64) (k : Nat) :
    serializedWord read k=SharedCodec.serializedWord read k := by rfl

theorem inflatedAt_of_words (s : MachineState) (b : SharedCodec.CBytes)
    (hw : ∀ k, k < 664 → s.getMem (BitVec.ofNat 64 (0x7000+8*k))=
      serializedWord (fun j=>b.extractLsb' (64*j) 64) k) : InflatedAt s b := by
  intro k hk
  have hlo:=hw (2*k) (by omega)
  have hhi:=hw (2*k+1) (by omega)
  rw [serializedWord_eq] at hlo hhi
  constructor
  · rw [show 0x7000+16*k=0x7000+8*(2*k) by omega]
    exact hlo.trans (by simpa only [Nat.add_zero,Nat.mul_zero] using
      SharedCodec.serializedWord_digC b k 0 (by decide))
  · rw [show 0x7000+16*k+8=0x7000+8*(2*k+1) by omega]
    exact hhi.trans (by simpa only [Nat.mul_one] using
      SharedCodec.serializedWord_digC b k 1 (by decide))

#print axioms serializedWord_congr
#print axioms hints_word
#print axioms inflatedAt_of_words
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem rawAt_of_fields {s : MachineState} {index : Nat} {raw : Fin 9→Fin 128}
    {ranks : Fin 9→Fin 563} (hf : SharedForestRun.Fields index raw ranks s) : RawAt s raw := by
  intro k
  convert hf.raw k using 1 <;> fin_cases k <;> rfl

theorem ScatterInv.forest_pre (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (index : Nat) (s t u : MachineState)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (ht : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hfields : SharedForestRun.Fields index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s)
    (uf : Frame t u (fun _=>False)) (up : u.pc=pcOf 46513)
    (hz : ∀ (off : Nat), off + 8 ≤ 8256 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (1216+off))=0)
    (hc3 : witness.counters 3=0) :
    SharedForestRun.Inv (Paired.witEnc output witness) index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) u 0
      (SharedV3.initialPair (Paired.witEnc output witness)) u := by
  have hframe:Frame s u ScatterW:=
    (ht.frame.trans uf).mono (by intro A hA h;rcases h with h|h;exact h;exact h.elim)
  apply SharedForestRun.initial_of_original _ _ _ _ u up
  · exact SharedForestRun.fields_frame hframe hfields
  · intro A hA hB h8
    have ho:A-1216+8≤8256:=by omega
    have he:1216+(A-1216)=A:=by omega
    have hw:=ScatterInv.original_prefix output witness b s t hin hforest ht hz (A-1216) ho
      (by omega) (Or.inr hc3)
    rw[he] at hw
    unfold W9Machine.OrigW at hw ⊢
    rw[uf.get (by omega) (fun h=>h)]
    exact hw
#print axioms rawAt_of_fields
#print axioms ScatterInv.forest_pre
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem hints_of_signature (s : MachineState) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*j))=b.extractLsb' (64*j) 64) :
    s.getMem 0x8478 >>> 48=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat := by
  have hh : s.getMem 0x8478=b.extractLsb' (64*655) 64 := hsig 655 (by decide)
  rw [hh,hints_word]
  change (b.extractLsb' (8*5246) 16).setWidth 64=BitVec.ofNat 64 (b.extractLsb' (8*5246) 16).toNat
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]

theorem inflatedAt_of_readout (s t : MachineState) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*j))=b.extractLsb' (64*j) 64)
    (hout : ∀ k, k < 664 → t.getMem (BitVec.ofNat 64 (0x7000+8*k))=
      serializedWord (fun j=>s.getMem (BitVec.ofNat 64 (0x7000+8*j))) k) : InflatedAt t b := by
  apply inflatedAt_of_words
  intro k hk
  exact (hout k hk).trans (serializedWord_congr _ _ k hk hsig)

theorem InflatedAt.frame {s t : MachineState} {b : SharedCodec.CBytes} (h : InflatedAt s b)
    {W : Nat→Prop} (hf : Frame s t W)
    (hn : ∀A,0x7000≤A → A<0x84c0 → ¬W A) : InflatedAt t b := by
  intro k hk
  have hh:=h k hk
  constructor
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.1
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.2
#print axioms hints_of_signature
#print axioms inflatedAt_of_readout
#print axioms InflatedAt.frame
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem scatter_forest_pre {im : Image} (hc : ∀k:Fin 9,CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) afterCode)
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (index : Nat) (s : MachineState) (hp : s.pc=pcOf 45257)
    (hin : SharedCompact.InflatedAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hfields : SharedForestRun.Fields index (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s)
    (hplan : PlanAt s) (hmode : s.getMem 417824=0)
    (hz : ∀ (off : Nat), off + 8 ≤ 8256 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (1216+off))=0)
    (hc3 : witness.counters 3=0) :
    ∃u, Steps im s 1256 1433 u ∧
      SharedForestRun.Inv (Paired.witEnc output witness) index (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) u 0
        (SharedV3.initialPair (Paired.witEnc output witness)) u ∧ Frame s u ScatterW := by
  obtain ⟨t,st,ht⟩:=scatter_steps hc s _ (rawAt_of_fields hfields) hplan hp
  obtain ⟨u,tu,up,ur,uf⟩:=after_steps ha t ht.pc
  have hm:t.getMem 417824=0:=by
    exact (ht.frame.get (A := 417824) (by decide) (by unfold ScatterW;omega)).trans hmode
  have hpc:u.pc=pcOf 46513:=by simpa only [hm,ite_true] using up
  have hframe:Frame s u ScatterW:=
    (ht.frame.trans uf).mono (by intro A hA h;rcases h with h|h;exact h;exact h.elim)
  refine ⟨u,st.trans tu,?_,hframe⟩
  exact ScatterInv.forest_pre output witness b index s t u hin hforest ht hfields uf hpc hz hc3
#print axioms scatter_forest_pre
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def ForestAt (s : MachineState) (b : SharedCodec.CBytes) : Prop :=
  ∀k,k<118 → DigAt s (0x7000+16*k)
    (SharedCodec.inflatedRead (0:Digest) (SharedCodec.digC b) k)

theorem ForestAt.value {s : MachineState} {b : SharedCodec.CBytes} (h : ForestAt s b)
    (k : Fin 9) (i : Fin 6) :
    DigAt s (SharedScatter.coordSource k.val+16*i.val)
      (Paired.coordinateValues (SharedCodec.sigDecC b).forest k i) := by
  have hh:=h (1+13*k.val+i.val) (by have:=k.isLt;have:=i.isLt;omega)
  rw [inflated_coordinate_value] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega

theorem ForestAt.path {s : MachineState} {b : SharedCodec.CBytes} (h : ForestAt s b)
    (k : Fin 9) (level : Nat) (hl : level < if k.val<8 ∧ k.val%2=0 then 6 else 7) :
    DigAt s (SharedScatter.coordSource k.val+96+16*level)
      (Paired.coordinatePath (SharedCodec.sigDecC b).forest k level) := by
  have hb:level<7:=by split_ifs at hl <;> omega
  have hh:=h (1+13*k.val+6+level) (by have:=k.isLt;omega)
  rw [inflated_coordinate_path b k level hl] at hh
  convert hh using 1 <;> unfold SharedScatter.coordSource <;> omega
#print axioms ForestAt.value
#print axioms ForestAt.path
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.T3M Paired W9Machine
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem canonical_sourceReadout_forest (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s : MachineState) (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest) (k : Fin 9) :
    SourceReadout (witEnc output witness) s k.val
      (SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val) := by
  let child : Fin 128 := ⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
    coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
  have hc:child.val=SharedV3.physical k.val (SharedForest.rawChildFromOutput output k).val:=coordPhysical_source _ _
  rw[←hc]
  apply sourceReadout_of_fields (witEnc output witness) s k child
    (coordinateValues witness.signature.forest k) (coordinatePath witness.signature.forest k)
  · intro i;rw[hforest];exact hin.value k i
  · intro l hl
    rw[hforest]
    apply hin.path k l
    simp only [SharedV3.lastLevel,SharedV3.first,decide_eq_true_eq] at hl
    split_ifs at hl ⊢ with h <;> simp_all
  · exact wchainValue_witEnc output witness k
  · exact wleafValue_witEnc output witness k
  · intro l hl
    rw[hc]
    exact wsibling_witEnc output witness k l hl
  · rw[hc]
    exact wtopOther_witEnc output witness k
#print axioms canonical_sourceReadout_forest
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedScatter
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.Research W9Machine
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ScatterInv.original_prefix_forest (output : HashOutput) (witness : SharedForest.Witness)
    (b : SharedCodec.CBytes) (s t : MachineState)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hi : ScatterInv s (SharedForest.rawChildFromOutput output) 9 t)
    (hz : ∀ (off : Nat), off + 8 ≤ 8256 → off % 8 = 0 → s.getMem (BitVec.ofNat 64 (1216+off))=0)
    (off : Nat) (hb : off+8≤8256) (ha : off%8=0) (hc : off≠32∨witness.counters 3=0) :
    W9Machine.OrigW (Paired.witEnc output witness) t (1216+off) := by
  let writes := fun A => ∃k:Fin 9,k.val<9 ∧
    PreciseCoordinateW k.val (coordPhysical k.val (SharedForest.rawChildFromOutput output k).val) A
  apply PairedReadout.original_prefix_of_slots output witness s t writes _ _ _ hz off hb ha hc
  · intro p hp half hh
    obtain ⟨k,hk,hp⟩:=List.mem_flatMap.mp hp
    refine ⟨k,k.isLt,?_⟩
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply rawSlots_written k child (Paired.coordinateValues witness.signature.forest k)
      (Paired.coordinatePath witness.signature.forest k) p _ half hh
    simpa only [Paired.coordinateSlots,rawSlots,child,coordPhysical_source] using hp
  · intro A hA
    obtain ⟨k,hk,hw⟩:=hA
    let child:Fin 128:=⟨coordPhysical k.val (SharedForest.rawChildFromOutput output k).val,
      coordPhysical_lt k.val (SharedForest.rawChildFromOutput output k)⟩
    apply CoordinateReadout.original k child (hi.readout k hk) _ A hw
    simpa only [child,coordPhysical_source] using canonical_sourceReadout_forest output witness b s hin hforest k
  · intro A hA hn
    exact hi.exactFrame.get hA hn
#print axioms ScatterInv.original_prefix_forest
end ClaudeWCT.W9.Machine.Expand.SharedScatter

namespace ClaudeWCT.W9.Machine.Expand.SharedCompact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M

theorem InflatedAt.forest {s:MachineState} {b:SharedCodec.CBytes} (h:InflatedAt s b) : ForestAt s b :=
  fun k hk=>h k (by omega)

theorem ForestAt.frame {s t:MachineState} {b:SharedCodec.CBytes} (h:ForestAt s b)
    {W:Nat → Prop} (hf:Frame s t W)
    (hn:∀A,0x7000≤A → A<0x7760 → ¬W A) : ForestAt t b := by
  intro k hk
  have hh:=h k hk
  constructor
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.1
  · rw[hf.get (by omega) (hn _ (by omega) (by omega))]
    exact hh.2
#print axioms InflatedAt.forest
#print axioms ForestAt.frame
end ClaudeWCT.W9.Machine.Expand.SharedCompact

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (DIG)
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def Work (A : Nat) : Prop :=
  A=SharedCompact.policyAddress ∨ (0x70d0≤A ∧ A<0x84c0) ∨ Writes A

structure Prepared (s0:MachineState) (message:SigGolfCandidate.T3.Message) (b:SharedCodec.CBytes) (s:MachineState) : Prop where
  pc : s.pc=pcOf 45056
  x5 : s.getReg .x5=0
  rho : DigAt s DIG (SharedCodec.sigDecC b).rho
  msg : ∀k,k < 4 → s.getMem (BitVec.ofNat 64 (DIG+32+8*k))=message.extractLsb' (64*k) 64
  inflated : SharedCompact.InflatedAt s b
  hints : s.getMem (BitVec.ofNat 64 SharedCompact.policyAddress)=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  data : SharedInit.DataAt s
  frame : Frame s0 s Work
  setupZero : ∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0

theorem prepare {im:Image} (he:CodeAt im (pcOf 0) [SharedCompact.entryWord])
    (hc:SharedCompact.AdapterCodeAt im) (hf:CodeAt im (pcOf 1) frontTail)
    (hz:CodeAt im (pcOf 42719) zeroBlk) (hj:CodeAt im (pcOf 30) [0x7892b06f])
    (s:MachineState) (message:SigGolfCandidate.T3.Message) (b:SharedCodec.CBytes)
    (hp:s.pc=pcOf 0) (h5:s.getReg .x5=0)
    (hb:∀k,k < 656 → s.getMem (BitVec.ofNat 64 (0x7000+8*k))=b.extractLsb' (64*k) 64)
    (hm:∀k,k < 4 → s.getMem (BitVec.ofNat 64 (0x65E0+8*k))=message.extractLsb' (64*k) 64)
    (hd:SharedInit.DataAt s) (hh:(SharedCodec.sigDecC b).policyHints.toNat<5832) :
    ∃t,Steps im s 3249 3249 t ∧ Prepared s message b t := by
  obtain ⟨u,su,up,uz,ur,uh,ub,uf⟩:=SharedCompact.front_readout he hc s hp
    (SharedCodec.sigDecC b).policyHints.toNat hh (SharedCompact.hints_of_signature s b hb)
  have ui:SharedCompact.InflatedAt u b:=SharedCompact.inflatedAt_of_readout s u b hb ub
  obtain ⟨t,ut,tp,t5,t0,t8,tm,tz,tr,tf⟩:=setup hf hz hj u up (ur.get (by decide) |>.trans h5)
  refine ⟨t,su.trans ut,⟨tp,t5,?_,?_,?_,?_,?_,?_,tz⟩⟩
  · have hr:=ui 0 (by decide)
    change DigAt u 0x7000 (SharedCodec.sigDecC b).rho at hr
    exact ⟨(t0 DIG (Or.inr rfl)).trans hr.1,(t8 (DIG+8) (Or.inr rfl)).trans hr.2⟩
  · intro k hk
    exact (tm k hk).trans ((uf.get (by omega) (by unfold SharedCompact.policyAddress;omega)).trans (hm k hk))
  · exact ui.frame tf (by intro A hA hB hw;unfold Writes at hw;simp only [DIG] at hw;omega)
  · exact (tf.get (by unfold SharedCompact.policyAddress;omega) (by unfold Writes SharedCompact.policyAddress DIG;omega)).trans uh
  · intro i hi
    have x:=hd i hi
    have hm : t.getByte (BitVec.ofNat 64 (SharedInit.DB+i))=s.getByte (BitVec.ofNat 64 (SharedInit.DB+i)) :=
      (uf.trans tf).getByte (by unfold SharedInit.DB;omega) (by
        intro h;rcases h with h|h
        · unfold SharedCompact.policyAddress SharedInit.DB at h;omega
        · unfold Writes SharedInit.DB DIG at h;omega)
    exact hm.trans x
  · exact (uf.trans tf).mono (by
      intro A hA h
      rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h))

#print axioms prepare
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem DataAt.frame {s t:MachineState} {W:Nat → Prop} (h:DataAt s)
    (hf:Frame s t W) (hn:∀A,DB≤A → A<DB+2160 → ¬W A) : DataAt t := by
  intro i hi
  have hm : t.getByte (BitVec.ofNat 64 (DB+i))=s.getByte (BitVec.ofNat 64 (DB+i)) :=
    hf.getByte (by unfold DB;omega) (hn _ (by unfold DB;omega) (by unfold DB;omega))
  exact hm.trans (h i hi)
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedFront
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Sign
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def SearchWrites (A:Nat) : Prop := Work A ∨ SharedDigest.writes A
structure Searched (s0:MachineState) (b:SharedCodec.CBytes)
    (r:Option (BitVec 32 × BitVec 256)) (s:MachineState) : Prop where
  x5 : s.getReg .x5=0
  inflated : SharedCompact.InflatedAt s b
  hints : s.getMem (BitVec.ofNat 64 SharedCompact.policyAddress)=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat
  data : SharedInit.DataAt s
  frame : Frame s0 s SearchWrites
  setupZero : ∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0
  result : match r with
    | none => s.pc=pcOf (SharedDigest.fail true)
    | some (c,a) => s.pc=pcOf (SharedDigest.accepted true) ∧ s.getReg .x19=BitVec.ofNat 64 c.toNat ∧
      c.toNat < 2^21 ∧ SigGolfCandidate.Research.SharedForest.digestAccepted a=true ∧ OutAt s SigGolfCandidate.T3M.Search.NBUF a

  resultR17 : match r with
    | none => True
    | some _ => s.getReg .x17=BitVec.ofNat 64 SigGolfCandidate.T3M.Search.NBUF

theorem search_prepared {im:Image} {sk:BitVec 256}
    (hl:LookOK im (SharedDigest.look true))
    {s0 s:MachineState} {message:SigGolfCandidate.T3.Message} {b:SharedCodec.CBytes}
    (hp:Prepared s0 message b s) :
    TBSim im sk s (2^21*200+12)
      (SigGolfCandidate.Research.SharedForest.sharedDigestSearch (SharedCodec.sigDecC b).rho message 0 (2^21))
      (Searched s0 b) := by
  have hpre:SharedDigest.Pre true (SharedCodec.sigDecC b).rho message s:=
    ⟨hp.x5,hp.rho,hp.msg,hp.data.tables⟩
  exact (SharedDigest.search_good true hl hpre hp.pc).mono (by omega) (by
    intro r t ht
    refine ⟨ht.x5,?_,?_,?_,hp.frame.trans ht.frame,?_,?_,?_⟩
    · exact hp.inflated.frame ht.frame (by intro A hA hB hw;simp only [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF] at hw;omega)
    · exact (ht.frame.get (by unfold SharedCompact.policyAddress;omega)
        (by simp only [SharedDigest.writes,SharedCompact.policyAddress,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF];omega)).trans hp.hints
    · exact hp.data.frame ht.frame (by intro A hA hB hw;simp only [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF] at hw;unfold SharedInit.DB at hA hB;omega)
    · intro A ha
      rw [ht.frame.get (by rcases ha with rfl|rfl|rfl|rfl <;> decide)
        (by rcases ha with rfl|rfl|rfl|rfl <;> simp [SharedDigest.writes,ClaudeWCT.W9.Machine.Sign.DIG,ClaudeWCT.W9.Machine.Sign.NBUF,SigGolfCandidate.T3M.Search.DIG,SigGolfCandidate.T3M.Search.NBUF])]
      exact hp.setupZero A ha
    · cases r with
      | none => exact ht.result.1
      | some p => exact ht.result
    · cases r <;> exact ht.resultR17)
#print axioms search_prepared
end ClaudeWCT.W9.Machine.Expand.SharedFront

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem legacyByte {im : Image} (hlen : im.data.length = 29808)
    (pre : List (BitVec 8)) (hp : pre.length = 25712)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) (i : Nat) (hi : i < 4096) :
    (w9init im m pk b).getByte (BitVec.ofNat 64 (TOP_DATA + i)) = Images.expandLegacyData.getD i 0 := by
  rw [show TOP_DATA + i = DB + (25712+i) by unfold TOP_DATA DB; omega,
    dataByte hlen (dataBase_of_length hlen) m pk b _ (by omega), hd]
  exact getD_prefixed pre Images.expandLegacyData 25712 i hp

theorem initial_tables_of_data {im : Image} (hlen : im.data.length = 29808)
    (pre : List (BitVec 8)) (hp : pre.length = 25712)
    (hd : im.data = pre ++ Images.expandLegacyData)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    TableOK (w9init im m pk b) ∧ CfTableOK 0 (w9init im m pk b) ∧
      Reward.RewardTablesOK (w9init im m pk b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_table i hi
  · intro i hi hj
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_cf i hi hj
  · intro i hi hj
    rw [legacyByte hlen pre hp hd m pk b i (by omega)]
    exact expandLegacyData_reward i hi hj

theorem initial_tables (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    TableOK (w9init Images.expandImage m pk b) ∧ CfTableOK 0 (w9init Images.expandImage m pk b) ∧
      Reward.RewardTablesOK (w9init Images.expandImage m pk b) := by
  exact initial_tables_of_data Images.expandData_length
    (Images.expandSharedData ++ Images.expandPrefixData)
    (by simp only [List.length_append, Images.expandSharedData_length, Images.expandPrefixData_length])
    (by rfl) m pk b
#print axioms initial_tables
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Layer Digest chainCount height)
open ClaudeWCT.W9.T3M
open SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem inflated_main (b : SharedCodec.CBytes) (i : Nat) (hi : 114 ≤ i) :
    SharedCodec.inflatedRead (0 : Digest) (SharedCodec.digC b) (i+4)=SharedCodec.digC b i := by
  unfold SharedCodec.inflatedRead SharedCodec.internalDummy SharedCodec.externalFullIndex
  simp only [show ¬(i+4=13 ∨ i+4=39 ∨ i+4=65 ∨ i+4=91) by omega,decide_false,Bool.false_eq_true,if_false,
    if_pos (show 13 < i+4 by omega),if_pos (show 39 < i+4 by omega),if_pos (show 65 < i+4 by omega),if_pos (show 91 < i+4 by omega)]
  congr 1

theorem lP_shared (lay : Layer) :
    SigGolfCandidate.T3M.Expand.lP lay=30864+16*(SharedCodec.layIdx lay-114) ∧
    114 ≤ SharedCodec.layIdx lay ∧ SharedCodec.layIdx lay+chainCount lay+height lay ≤ 328 := by
  fin_cases lay <;> decide

theorem main_readout {b : SharedCodec.CBytes} {s t : MachineState}
    (hsource : SharedCompact.InflatedAt s b)
    (hmove : ∀i<428,t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i))) :
    SigGolfCandidate.T3M.Expand.BC.SigLayersAt t (SharedForest.mainSignature (SharedCodec.sigDecC b)) := by
  have hrows : ∀i<214,DigAt t (30864+16*i) (SharedCodec.digC b (114+i)) := by
    intro i hi
    have h:=hsource (118+i) (by omega)
    rw [show 118+i=(114+i)+4 by omega,inflated_main b _ (by omega)] at h
    have ha:0x7000+16*(114+i+4)=30560+16*i:=by omega
    rw [ha] at h
    refine ⟨?_,?_⟩
    · have hm:=hmove (2*i) (by omega)
      rw [show 30864+8*(2*i)=30864+16*i by omega,show 30560+8*(2*i)=30560+16*i by omega] at hm
      exact hm.trans h.1
    · have hm:=hmove (2*i+1) (by omega)
      rw [show 30864+8*(2*i+1)=30864+16*i+8 by omega,show 30560+8*(2*i+1)=30560+16*i+8 by omega] at hm
      exact hm.trans h.2
  intro lay
  obtain ⟨hp,hl,hh⟩:=lP_shared lay
  constructor
  · intro i hi
    have h:=hrows (SharedCodec.layIdx lay-114+i) (by omega)
    rw [show 114+(SharedCodec.layIdx lay-114+i)=SharedCodec.layIdx lay+i by omega,
      show 30864+16*(SharedCodec.layIdx lay-114+i)=SigGolfCandidate.T3M.Expand.lP lay+16*i by rw[hp];omega] at h
    exact h
  · intro j hj
    have h:=hrows (SharedCodec.layIdx lay-114+chainCount lay+j) (by omega)
    rw [show 114+(SharedCodec.layIdx lay-114+chainCount lay+j)=SharedCodec.layIdx lay+chainCount lay+j by omega,
      show 30864+16*(SharedCodec.layIdx lay-114+chainCount lay+j)=SigGolfCandidate.T3M.Expand.lP lay+16*chainCount lay+16*j by rw[hp];omega] at h
    exact h
#print axioms main_readout
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open SigGolfCandidate.T3M.Search (ENC NODE)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def Writes (A : Nat) : Prop :=
  A=0x20260 ∨ A=0x20268 ∨ A=0x20290 ∨ A=0x20298 ∨ (2048≤A ∧ A<2112) ∨ (30864≤A ∧ A<34288)

theorem layer_inv {b : SharedCodec.CBytes} {s t : MachineState} {index : Nat} {pair : Digest × Digest}
    (hp : t.pc=pcOf 249) (h5 : t.getReg .x5=0) (hi : index<2^31)
    (hidx : s.getMem (BitVec.ofNat 64 SigGolfCandidate.T3M.Expand.IDXV)=BitVec.ofNat 64 index)
    (hin : SharedCompact.InflatedAt s b)
    (hL : DigAt s 1216 pair.1) (hR : DigAt s 1264 pair.2)
    (hroots : ∀o,(o=0 ∨ o=8 ∨ o=48 ∨ o=56) → t.getMem (BitVec.ofNat 64 (0x20260+o))=s.getMem (BitVec.ofNat 64 (1216+o)))
    (hmove : ∀i,i<428 → t.getMem (BitVec.ofNat 64 (30864+8*i))=s.getMem (BitVec.ofNat 64 (30560+8*i)))
    (hf : Frame s t Writes)
    (hc32 : ∃x<2^32,s.getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x)
    (hz : SigGolfCandidate.T3M.Expand.BC.LZero s)
    (htab : Search.TableOK s) (hcf : Search.CfTableOK 0 s) (hrew : Search.Reward.RewardTablesOK s)
    (hhint : (SharedCodec.sigDecC b).policyHints.toNat<5832)
    (hhmem : s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat) :
    SigGolfCandidate.T3M.Expand.SharedLayers.LInv (SharedForest.mainSignature (SharedCodec.sigDecC b))
      (SharedCodec.sigDecC b).policyHints index 4 (.pair pair.1 pair.2) t := by
  have keep (A : Nat) (ha : A<2^64) (hw : ¬Writes A) := hf.get ha hw
  refine ⟨⟨hp,by decide,h5,hi,?_,?_,?_,?_,?_,main_readout hin hmove,?_,?_,?_,?_⟩,hhint,?_⟩
  · exact (keep _ (by decide) (by unfold Writes; decide)).trans hidx
  · exact ⟨(hroots 0 (by simp)).trans hL.1,(hroots 8 (by simp)).trans hL.2⟩
  · intro _
    exact ⟨(hroots 48 (by simp)).trans hR.1,(hroots 56 (by simp)).trans hR.2⟩
  · intro h;omega
  · rcases hc32 with ⟨x,hx,hm⟩
    exact ⟨x,hx,(keep _ (by decide) (by unfold Writes; decide)).trans hm⟩
  · exact ⟨(keep _ (by decide) (by unfold Writes; decide)).trans hz.c0,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.c8,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.c32,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.c40,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.n32,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.n40,
      (keep _ (by decide) (by unfold Writes; decide)).trans hz.e40⟩
  · exact htab.frame hf (by intro i hi;unfold Writes Search.TOP_DATA;omega)
  · exact hcf.frame hf (by intro i hi hj;unfold Writes Search.TOP_DATA;omega)
  · exact hrew.frame hf (by intro i hi hj;unfold Writes Search.TOP_DATA;omega)
  · exact (keep _ (by decide) (by unfold Writes; decide)).trans hhmem
#print axioms layer_inv
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

theorem shifted_data_mem {im ref : Image} (hlen : im.data.length=29808)
    (pre : List (BitVec 8)) (hp : pre.length=2160) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : Bytes 5248)
    (A : Nat) (hlo : Compact2.LPLAN≤A) (hhi : A<Compact2.LPLAN+27648) (hal : A%8=0) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A)=
      (w9init ref m pk (0 : Bytes 5312)).getMem (BitVec.ofNat 64 A) := by
  rw [getMem hlen (dataBase_of_length hlen) m pk b A (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_neg (by unfold Compact2.LPLAN at *;omega),
    if_neg (by unfold Compact2.LPLAN at *;omega),if_pos (by unfold Compact2.LPLAN DB at *;omega),
    w9init_data href m pk (0 : Bytes 5312) A hlo hhi (by unfold Compact2.LPLAN;omega),hd]
  rw [show A-DB=2160+(A-Compact2.LPLAN) by unfold DB Compact2.LPLAN at *;omega,
    ←List.drop_drop,List.drop_left' hp]

theorem initial_plans_of_data {im ref : Image} (hlen : im.data.length=29808)
    (pre : List (BitVec 8)) (hp : pre.length=2160) (hd : im.data=pre++ref.data)
    (href : ExpandDataOK ref) (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ClaudeWCT.W9.Machine.Expand.PlanAt (w9init im m pk b) ∧ Compact2.LPlanAt (w9init im m pk b) := by
  constructor
  · intro k hk
    rw [shifted_data_mem hlen pre hp hd href m pk b _ (by unfold PLAN Compact2.LPLAN;omega)
      (by unfold PLAN Compact2.LPLAN;omega) (by unfold PLAN;omega)]
    exact w9init_plan href m pk (0 : Bytes 5312) k hk
  · intro k hk
    rw [shifted_data_mem hlen pre hp hd href m pk b _ (by omega)
      (by unfold Compact2.LPLAN;omega) (by unfold Compact2.LPLAN;omega)]
    exact w9init_lplan href m pk (0 : Bytes 5312) k hk

theorem reference_data_ok : ExpandDataOK (⟨[],Images.expandPrefixData++Images.expandLegacyData⟩ : Image) := by
  change Images.expandPrefixData++Images.expandLegacyData = _
  have hp : Images.expandPrefixData = lplanBytes++planBytes++expCostBytes++hdrBankBytes := by
    unfold Images.expandPrefixData lplanBytes planBytes expCostBytes hdrBankBytes
    rw [←List.flatten_append,←List.flatten_append,←List.flatten_append]
    rfl
  rw [hp]

theorem initial_plans (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ClaudeWCT.W9.Machine.Expand.PlanAt (w9init Images.expandImage m pk b) ∧
      Compact2.LPlanAt (w9init Images.expandImage m pk b) := by
  exact initial_plans_of_data (ref:=⟨[],Images.expandPrefixData++Images.expandLegacyData⟩)
    Images.expandData_length Images.expandSharedData Images.expandSharedData_length
    (by change (Images.expandSharedData++Images.expandPrefixData)++Images.expandLegacyData = _;rw[List.append_assoc])
    reference_data_ok m pk b
#print axioms initial_plans
end ClaudeWCT.W9.Machine.Expand.SharedInit

namespace ClaudeWCT.W9.Machine.Expand.SharedHandoff
open ClaudeWCT.W9.T3M SigGolfCandidate.Research

theorem decoded_projection (b : SharedCodec.CBytes) :
    SharedForest.fillTopSignature (SharedCodec.sigDecC b) 0 = SharedCodec.sigDecC b := by
  have hset (x : BitVec 112) : ClaudeWCT.WCT9.setTop (x.setWidth 128) 0=x.setWidth 128 := by
    apply BitVec.eq_of_toNat_eq
    have hx := x.isLt
    simp only [ClaudeWCT.WCT9.setTop,BitVec.toNat_ofNat,BitVec.toNat_setWidth,
      Nat.zero_mod,Nat.zero_mul,Nat.add_zero]
    omega
  apply congrArg (fun layers => SharedForest.Signature.mk (SharedCodec.sigDecC b).rho
    (SharedCodec.sigDecC b).policyHints (SharedCodec.sigDecC b).forest layers)
  funext lay
  apply congrArg (fun path => SigGolfCandidate.T3.LayerSignature.mk
    ((SharedCodec.sigDecC b).layers lay).values path)
  funext j
  change (if lay.val=0 ∧ j.val=11 then
    ClaudeWCT.WCT9.setTop (((SharedCodec.sigDecC b).layers lay).path j) 0 else
    ((SharedCodec.sigDecC b).layers lay).path j) = _
  split
  next h =>
    have hl : lay=0 := Fin.ext h.1
    subst lay
    have hj : j.val=11 := h.2
    simpa only [SharedCodec.sigDecC,SharedCodec.layIdx,List.getElem_cons_zero,
      Matrix.cons_val_zero,SigGolfCandidate.T3.chainCount,hj,Nat.reduceAdd,
      SharedCodec.digC,show ¬(179<179) by decide,if_false,if_pos rfl,ite_true] using
      hset (b.extractLsb' (128*327) 112)
  next => rfl

theorem main_projection (b : SharedCodec.CBytes) :
    ClaudeWCT.WCT9.fillTop (SharedForest.mainSignature (SharedCodec.sigDecC b)) 0 =
      SharedForest.mainSignature (SharedCodec.sigDecC b) := by
  exact congrArg SharedForest.mainSignature (decoded_projection b)

#print axioms decoded_projection
#print axioms main_projection
end ClaudeWCT.W9.Machine.Expand.SharedHandoff

namespace ClaudeWCT.W9.Machine.Expand.SharedInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (ENC NODE)
open SigGolfCandidate.T3M.Expand (CHAIN)
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem public_key_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    DigAt (w9init im m pk b) 0xA0 pk := by
  have hword (i : Nat) (hi : i<2) :
      (w9init im m pk b).getMem (BitVec.ofNat 64 (0xA0+8*i))=pk.extractLsb' (64*i) 64 := by
    rw [getMem hlen (dataBase_of_length hlen) m pk b _ (by omega),
      if_neg (by omega),if_pos (by omega),show 0xA0+8*i-0xA0=8*i by omega]
    exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_e pk i (by omega)
  exact ⟨hword 0 (by decide),hword 1 (by decide)⟩

theorem region_zero_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∀A,0x2c48≤A → A<0x61c8 → (w9init im m pk b).getMem (BitVec.ofNat 64 A)=0 := by
  intro A hlo hhi
  exact zero hlen (dataBase_of_length hlen) m pk b A
    (by unfold DB;omega) (Or.inl (by omega)) (Or.inr (by omega)) (Or.inl (by omega))

theorem layer_zero_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    SigGolfCandidate.T3M.Expand.BC.LZero (w9init im m pk b) := by
  constructor <;> apply zero hlen (dataBase_of_length hlen) m pk b <;>
    simp only [CHAIN,NODE,ENC,DB] <;> omega

theorem counter_of_length {im : Image} (hlen : im.data.length=29808)
    (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    ∃x<2^32,(w9init im m pk b).getMem (BitVec.ofNat 64 (ENC+32))=BitVec.ofNat 64 x := by
  refine ⟨0,by decide,?_⟩
  apply zero hlen (dataBase_of_length hlen) m pk b <;> simp only [ENC,DB] <;> omega

theorem initial_thresholds (m : Message) (pk : PublicKey) (b : Bytes 5248) :
    (∀r,r<48 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749456+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 1 r)) ∧
    (∀r,r<35 → (w9init Images.expandImage m pk b).getByte (BitVec.ofNat 64 (16749520+r))=
      BitVec.ofNat 8 (ClaudeWCT.WCT9.CanonicalPolicy.threshold 2 r)) := by
  have h : SharedValidate.Tables (w9init Images.expandImage m pk b) := initial_data m pk b
  exact ⟨h.first,h.second⟩

#print axioms public_key_of_length
#print axioms region_zero_of_length
#print axioms layer_zero_of_length
#print axioms counter_of_length
#print axioms initial_thresholds
end ClaudeWCT.W9.Machine.Expand.SharedInit
