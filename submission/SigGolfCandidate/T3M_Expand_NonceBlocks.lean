import SigGolfCandidate.T3M_Expand_LayerChain

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
