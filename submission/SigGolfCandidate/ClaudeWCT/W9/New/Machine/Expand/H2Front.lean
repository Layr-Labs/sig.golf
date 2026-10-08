import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.ComposeBack

/-! # H2 expander prologue: the compact signature, un-shifted in place

Word 0 jumps to the prologue (words 42777..42794): it keeps the 14 tail bytes (sig 5440..5455, read as two words;
bytes 5454/5455 are zero), moves sig [3072, 5440) up by 16 bytes (backwards, one word per step), stores the kept
words at sig 3072 (the top sibling with its two omitted bytes zero), clears its scratch registers and jumps to word
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
  [36535, 1410240147, 963331, 9352067, 36663, 3222212371, 4287532691, 964227, 14596131, 4292831971, 7286819,
    8336419, 787, 915, 3731, 3859, 1683, 3050135663]
def proA : List (BitVec 32) := [36535, 1410240147, 963331, 9352067, 36663, 3222212371]
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
      t.getReg .x29 = BitVec.ofNat 64 0x8540 ∧ t.getReg .x30 = BitVec.ofNat 64 0x7c00 ∧
      t.getReg .x6 = s.getMem (BitVec.ofNat 64 0x8540) ∧ t.getReg .x7 = s.getMem (BitVec.ofNat 64 0x8548) ∧
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

theorem m64_add8 (X : Nat) (h : X ≤ 34112) : (X + 8) % 18446744073709551616 = X + 8 :=
  Nat.mod_eq_of_lt (by omega)
theorem m64_sub8 (X : Nat) (hX : 8 ≤ X) (h : X ≤ 34112) :
    (X + 18446744073709551608) % 18446744073709551616 = X - 8 := by
  rw [show X + 18446744073709551608 = (X - 8) + 18446744073709551616 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)
theorem ofNat_m8 (X : Nat) (hX : 8 ≤ X) (h : X ≤ 34112) :
    BitVec.ofNat 64 (X + 18446744073709551608) = BitVec.ofNat 64 (X - 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [m64_sub8 X hX h, Nat.mod_eq_of_lt (show X - 8 < 18446744073709551616 by omega)]

theorem proL_spec {im : Image} (hP : ProAt im) (s : MachineState) (hpc : s.pc = pcOf 42783) (X : Nat)
    (hX8 : X % 8 = 0) (hX : 0x7c08 ≤ X) (hX' : X ≤ 0x8540)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) (h30 : s.getReg .x30 = BitVec.ofNat 64 0x7c00) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = (if 0x7c00 < X - 8 then pcOf 42783 else pcOf 42787) ∧
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
    rw [Nat.mod_eq_of_lt (show 31744 < 18446744073709551616 by norm_num),
      Nat.mod_eq_of_lt (show X - 8 < 18446744073709551616 by omega)]
    by_cases hc : 31744 < X - 8 <;> simp [hc, pcOf]
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
    (h30 : s.getReg .x30 = BitVec.ofNat 64 0x7c00) :
    ∃ t, Steps im s 7 7 t ∧ t.pc = pcOf 42794 ∧
      t.getMem (BitVec.ofNat 64 0x7c00) = s.getReg .x6 ∧ t.getMem (BitVec.ofNat 64 0x7c08) = s.getReg .x7 ∧
      t.getReg .x6 = 0 ∧ t.getReg .x7 = 0 ∧ t.getReg .x29 = 0 ∧ t.getReg .x30 = 0 ∧ t.getReg .x13 = 0 ∧
      RegsExcept s t [.x6, .x7, .x13, .x29, .x30] ∧ Frame s t (fun A => A = 0x7c00 ∨ A = 0x7c08) := by
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
  x29 : t.getReg .x29 = BitVec.ofNat 64 (0x8540 - 8 * i)
  x30 : t.getReg .x30 = BitVec.ofNat 64 0x7c00
  x6 : t.getReg .x6 = s0.getMem (BitVec.ofNat 64 0x8540)
  x7 : t.getReg .x7 = s0.getMem (BitVec.ofNat 64 0x8548)
  hi : i ≤ 296
  moved : ∀ j < i, t.getMem (BitVec.ofNat 64 (0x8548 - 8 * j)) = s0.getMem (BitVec.ofNat 64 (0x8538 - 8 * j))
  regs : RegsExcept s0 t [.x6, .x7, .x13, .x29, .x30]
  frame : Frame s0 t (fun A => ∃ j < i, A = 0x8548 - 8 * j)

theorem proLoop {im : Image} (hP : ProAt im) {s0 u : MachineState} (h0 : PInv s0 0 u) :
    ∀ i, i ≤ 295 → ∃ t, Steps im u (4 * i) (4 * i) t ∧ PInv s0 i t := by
  intro i
  induction i with
  | zero => intro _; exact ⟨u, Steps.refl u, h0⟩
  | succ i ih =>
    intro hi
    obtain ⟨t, st, ht⟩ := ih (by omega)
    obtain ⟨t', st', p', x29', m', r', f'⟩ := proL_spec hP t ht.pc (0x8540 - 8 * i) (by omega) (by omega) (by omega)
      ht.x29 ht.x30
    rw [if_pos (by omega)] at p'
    refine ⟨t', (st.trans st').of_eq (by ring) (by ring), ⟨p', by rw [x29', show 34112 - 8 * i - 8 = 34112 - 8 * (i + 1) by omega],
      by rw [r'.get (by decide)]; exact ht.x30, by rw [r'.get (by decide)]; exact ht.x6,
      by rw [r'.get (by decide)]; exact ht.x7, by omega, fun j hj => ?_, (ht.regs.trans r').mono (by decide),
      fun A hA hn => ?_⟩⟩
    · by_cases hji : j < i
      · rw [f'.get (by omega) (by omega)]; exact ht.moved j hji
      · have hj : j = i := by omega
        subst hj
        rw [show 0x8548 - 8 * j = 0x8540 - 8 * j + 8 by omega, m',
          show 0x8540 - 8 * j - 8 = 0x8538 - 8 * j by omega,
          ht.frame.get (by omega) (by rintro ⟨j', hj', e⟩; omega)]
    · rw [f'.get hA (fun h => hn ⟨i, by omega, by omega⟩),
        ht.frame.get hA (fun ⟨j, hj, e⟩ => hn ⟨j, by omega, e⟩)]

/-- The whole prologue, from reset to word 1. -/
theorem prologue_spec {im : Image} (hP : ProAt im) (s0 : MachineState) (hpc : s0.pc = pcOf 0)
    (hz : ∀ r, r ∈ [Reg.x6, .x7, .x13, .x29, .x30] → s0.getReg r = 0) :
    ∃ u, Steps im s0 1199 1199 u ∧ u.pc = pcOf 1 ∧ (∀ r, u.getReg r = s0.getReg r) ∧
      u.getMem (BitVec.ofNat 64 0x7c00) = s0.getMem (BitVec.ofNat 64 0x8540) ∧
      u.getMem (BitVec.ofNat 64 0x7c08) = s0.getMem (BitVec.ofNat 64 0x8548) ∧
      (∀ j < 296, u.getMem (BitVec.ofNat 64 (0x8548 - 8 * j)) = s0.getMem (BitVec.ofNat 64 (0x8538 - 8 * j))) ∧
      Frame s0 u (fun A => A = 0x7c00 ∨ A = 0x7c08 ∨ ∃ j < 296, A = 0x8548 - 8 * j) := by
  have s1 := w0_step hP s0 hpc
  set u1 := s0.setPC (pcOf 42777) with hu1
  obtain ⟨u2, s2, p2, x29, x30, x6, x7, r2, f2⟩ := proA_spec hP u1 rfl
  have h0 : PInv s0 0 u2 :=
    ⟨p2, by rw [x29], x30, by rw [x6]; rfl, by rw [x7]; rfl, by omega, fun j hj => absurd hj (by omega),
      fun r hr => by rw [r2.get (fun h => hr (by simp only [List.mem_cons, List.not_mem_nil, or_false] at h ⊢; tauto))]; rfl, fun A hA hn => by rw [f2.get hA (fun h => h)]; rfl⟩
  obtain ⟨u3, s3, h3⟩ := proLoop hP h0 295 le_rfl
  obtain ⟨u4, s4, p4, x29', m4, r4, f4⟩ := proL_spec hP u3 h3.pc (0x8540 - 8 * 295) (by decide) (by decide)
    (by decide) h3.x29 h3.x30
  rw [if_neg (by decide)] at p4
  have h4moved : ∀ j < 296, u4.getMem (BitVec.ofNat 64 (0x8548 - 8 * j)) =
      s0.getMem (BitVec.ofNat 64 (0x8538 - 8 * j)) := by
    intro j hj
    by_cases hji : j < 295
    · rw [f4.get (by omega) (by omega)]; exact h3.moved j hji
    · have hj : j = 295 := by omega
      subst hj
      rw [show 0x8548 - 8 * 295 = 0x8540 - 8 * 295 + 8 by decide, m4,
        show 0x8540 - 8 * 295 - 8 = 0x8538 - 8 * 295 by decide,
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

def sigFull (b : Bytes 5454) : Bytes 5456 := ClaudeWCT.W9.T3M.sigB (ClaudeWCT.W9.T3M.sigDecC b)
theorem sigDec_sigFull (b : Bytes 5454) : ClaudeWCT.W9.T3M.sigDec (sigFull b) = ClaudeWCT.W9.T3M.sigDecC b :=
  ClaudeWCT.W9.T3M.sigDec_sigB _
def cw (j : Nat) : Nat := if j < 384 then j else if j < 386 then j + 296 else j - 2

theorem extract_word {n : Nat} (x : BitVec n) (a i : Nat) (hi : i < 2) :
    (x.extractLsb' a 128).extractLsb' (64 * i) 64 = x.extractLsb' (a + 64 * i) 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 128 = 2 ^ (64 * i) * 2 ^ (128 - 64 * i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)), Nat.div_div_eq_div_mul,
    ← pow_add]

theorem sigFull_word (b : Bytes 5454) (j : Nat) (hj : j < 682) :
    (sigFull b).extractLsb' (64 * j) 64 = b.extractLsb' (64 * cw j) 64 := by
  have hk : j / 2 < 341 := by omega
  have e1 : (sigFull b).extractLsb' (64 * j) 64 =
      ((sigFull b).extractLsb' (128 * (j / 2)) 128).extractLsb' (64 * (j % 2)) 64 := by
    rw [extract_word _ _ _ (Nat.mod_lt _ (by decide))]; congr 1; omega
  have e2 : (sigFull b).extractLsb' (128 * (j / 2)) 128 = ClaudeWCT.W9.T3M.digC b (j / 2) := by
    show ClaudeWCT.W9.T3M.sigDig (sigFull b) (j / 2) = _
    rw [sigFull, ClaudeWCT.W9.T3M.sigDig_sigB, ClaudeWCT.W9.T3M.sigDigests_sigDecC b _ hk]
  rw [e1, e2]
  unfold ClaudeWCT.W9.T3M.digC ClaudeWCT.W9.T3M.cDig cw
  by_cases h1 : j / 2 < 192
  · rw [if_pos h1, extract_word _ _ _ (Nat.mod_lt _ (by decide)), if_pos (by omega)]; congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : j / 2 = 192
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
variable {im : Image} (hd : ExpandDataOK im) (m : Message) (pk : PublicKey) (b : Bytes 5454)
include hd
theorem w9initC_getMem (A : Nat) (hA : A < 2 ^ 64) :
    (w9init im m pk b).getMem (BitVec.ofNat 64 A) =
      if 0x7000 ≤ A ∧ A < 0x7000 + 5456 ∧ (A - 0x7000) % 8 = 0 then
        bytesToWordLE (((bytes b).drop (A - 0x7000)).take 8)
      else if 0xA0 ≤ A ∧ A < 0xB0 ∧ (A - 0xA0) % 8 = 0 then bytesToWordLE (((bytes pk).drop (A - 0xA0)).take 8)
      else if 0x5BF0 ≤ A ∧ A < 0x5C10 ∧ (A - 0x5BF0) % 8 = 0 then
        bytesToWordLE (((bytes m).drop (A - 0x5BF0)).take 8)
      else if Compact2.LPLAN ≤ A ∧ A < Compact2.LPLAN + 27648 ∧ (A - Compact2.LPLAN) % 8 = 0 then
        bytesToWordLE ((im.data.drop (A - Compact2.LPLAN)).take 8)
      else 0 := by
  unfold w9init
  rw [MachineState.getMem_setReg, getMem_writeBytesAsWords _ _ 0x7000 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0xA0 A (by rw [bytes_length_e]; decide) hA,
    getMem_writeBytesAsWords _ _ 0x5BF0 A (by rw [bytes_length_e]; decide) hA, dataBase_eq hd,
    getMem_writeBytesAsWords _ _ Compact2.LPLAN A (by rw [data_length hd]; decide) hA, bytes_length_e, bytes_length_e,
    bytes_length_e, data_length hd]
  rfl
theorem w9initC_word (j : Nat) (hj : j < 682) :
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
    (h70 : u.getMem (BitVec.ofNat 64 0x7c00) = (w9init im m pk b).getMem (BitVec.ofNat 64 0x8540))
    (h78 : u.getMem (BitVec.ofNat 64 0x7c08) = (w9init im m pk b).getMem (BitVec.ofNat 64 0x8548))
    (hmv : ∀ j < 296, u.getMem (BitVec.ofNat 64 (0x8548 - 8 * j)) =
      (w9init im m pk b).getMem (BitVec.ofNat 64 (0x8538 - 8 * j)))
    (hf : Frame (w9init im m pk b) u (fun A => A = 0x7c00 ∨ A = 0x7c08 ∨ ∃ j < 296, A = 0x8548 - 8 * j)) :
    ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) = (w9init im m pk (sigFull b)).getMem (BitVec.ofNat 64 A) := by
  intro A hA
  rw [w9init_getMem hd m pk (sigFull b) A hA]
  by_cases hs : 0x7000 ≤ A ∧ A < 0x7000 + 5456 ∧ (A - 0x7000) % 8 = 0
  · rw [if_pos hs]
    obtain ⟨j, rfl⟩ : ∃ j, A = 0x7000 + 8 * j := ⟨(A - 0x7000) / 8, by omega⟩
    have hj : j < 682 := by omega
    rw [show 0x7000 + 8 * j - 0x7000 = 8 * j by omega, bytesToWordLE_bytes_e (sigFull b) j (by omega),
      sigFull_word b j hj]
    unfold cw
    by_cases h1 : j < 384
    · rw [if_pos h1, hf.get hA (by rintro (h | h | ⟨j', hj', e⟩) <;> omega), w9initC_word hd m pk b j hj]
    · rw [if_neg h1]
      by_cases h2 : j < 386
      · rw [if_pos h2]
        by_cases h3 : j = 384
        · subst h3
          rw [h70, show (0x8540 : Nat) = 0x7000 + 8 * 680 from rfl, w9initC_word hd m pk b 680 (by decide)]
        · have h4 : j = 385 := by omega
          subst h4
          rw [h78, show (0x8548 : Nat) = 0x7000 + 8 * 681 from rfl, w9initC_word hd m pk b 681 (by decide)]
      · rw [if_neg h2]
        have := hmv (681 - j) (by omega)
        rw [show 0x8548 - 8 * (681 - j) = 0x7000 + 8 * j by omega,
          show 0x8538 - 8 * (681 - j) = 0x7000 + 8 * (j - 2) by omega, w9initC_word hd m pk b (j - 2) (by omega)]
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
      t.getMem (BitVec.ofNat 64 (DIG + 32)) = s.getMem (BitVec.ofNat 64 0x5BF0) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 40)) = s.getMem (BitVec.ofNat 64 0x5BF8) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 48)) = s.getMem (BitVec.ofNat 64 0x5C00) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 56)) = s.getMem (BitVec.ofNat 64 0x5C08) ∧
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
    (pk : PublicKey) (σ : Bytes 5456) (u : MachineState) (hupc : u.pc = pcOf 1) (hu5 : u.getReg .x5 = 0)
    (humem : ∀ A, A < 2 ^ 64 → u.getMem (BitVec.ofNat 64 A) = (w9init im m pk σ).getMem (BitVec.ofNat 64 A)) :
    ∃ t, Steps im u 36 36 t ∧ Pre30 m (sigDec σ) t ∧
      (∀ A, A < 2 ^ 64 → (A = 0x5BF0 ∨ A = 0x5BF8 ∨ A = 0x5C00 ∨ A = 0x5C08) → t.getMem (BitVec.ofNat 64 A) = 0) ∧
      t.getMem (BitVec.ofNat 64 0x800) = (sigDec σ).rho.extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 0x808) = (sigDec σ).rho.extractLsb' 64 64 ∧
      Frame (w9init im m pk σ) t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
        A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x5BF0 ∨ A = 0x5BF8 ∨ A = 0x5C00 ∨ A = 0x5C08) := by
  set s := w9init im m pk σ
  obtain ⟨t0, st0, p0, x5_0, w800, w808, d0, d8, d32, d40, d48, d56, r0, f0'⟩ := front_spec' hP u hupc hu5
  have f0 : Frame s t0 (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨
        A = DIG + 48 ∨ A = DIG + 56) :=
    fun A hA hn => (f0' A hA hn).trans (humem A hA)
  rw [humem 0x7000 (by decide)] at w800 d0
  rw [humem 0x7008 (by decide)] at w808 d8
  rw [humem 0x5BF0 (by decide)] at d32
  rw [humem 0x5BF8 (by decide)] at d40
  rw [humem 0x5C00 (by decide)] at d48
  rw [humem 0x5C08 (by decide)] at d56
  obtain ⟨t, st1, p, x19, z, r1, f1⟩ := zero_spec hF.2 t0 p0
  have f : Frame s t (fun A => A = 0x800 ∨ A = 0x808 ∨ A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨
      A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 ∨ A = 0x5BF0 ∨ A = 0x5BF8 ∨ A = 0x5C00 ∨ A = 0x5C08) :=
    (f0.trans f1).mono (fun A _ h => by
      rcases h with h | h
      · rcases h with h | h | h | h | h | h | h | h <;> simp [h]
      · rcases h with h | h | h | h <;> simp [h])
  have g : ∀ A, A < 2 ^ 64 → ¬ (A = 0x5BF0 ∨ A = 0x5BF8 ∨ A = 0x5C00 ∨ A = 0x5C08) →
      t.getMem (BitVec.ofNat 64 A) = t0.getMem (BitVec.ofNat 64 A) := fun A hA h => f1 A hA h
  have hrho : DigAt s 0x7000 (sigDec σ).rho := w9init_sig hd m pk σ 0 (by decide)
  have hsd : ∀ k, k < 341 → DigAt t (0x7000 + 16 * k) ((sigDigests (sigDec σ)).getD k 0) := by
    intro k hk
    have := w9init_sig hd m pk σ k hk
    rw [sigDigests_sigDec σ k hk]
    exact ⟨(f _ (by omega) (by simp only [DIG]; omega)).trans this.1,
      (f _ (by omega) (by simp only [DIG]; omega)).trans this.2⟩
  refine ⟨t, st0.trans st1, ⟨p, by rw [r1.get (by decide), x5_0], x19,
      ⟨(g _ (by decide) (by simp only [DIG]; omega)).trans (d0.trans hrho.1),
        (g _ (by decide) (by simp only [DIG]; omega)).trans (d8.trans hrho.2)⟩, fun k hk => ?_, hsd,
      fun A h1 h2 => ?_,
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

end ClaudeWCT.W9.Machine.Expand
end
