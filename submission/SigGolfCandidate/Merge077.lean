import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge076

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
-- ==== merged from T3M_Expand_Layer ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (NODE NOUT)
theorem bc_remaining {s : MachineState} {hh j : Nat} (hj : j < hh) (hh' : hh ≤ 12)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    BCBlocks.remaining s = BitVec.ofNat 64 (hh - j - 1) := by
  unfold BCBlocks.remaining
  rw [h15, h20, BitVec.ofNat_sub_ofNat_of_le hh j (by omega) (by omega)]
  change BitVec.ofNat 64 (hh - j) - BitVec.ofNat 64 1 = _
  exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) (by omega)
end SigGolfCandidate.T3M.Expand
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest Signature chain chainInput shortHash pad64 zero16 header chainCount height
  width maxDigit route recoverLayer leafHash nodeHash)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
set_option autoImplicit false
theorem chainCount_ne0 : ∀ l : Layer, l ≠ 0 → chainCount l = 43 := by decide
theorem chainCount_cases' (lay : Layer) : chainCount lay = 51 ∨ chainCount lay = 43 := by
  fin_cases lay <;> simp [chainCount]

theorem height_le (lay : Layer) : height lay ≤ 12 := by
  fin_cases lay <;> simp [height]
theorem csN4_le (lay : Layer) : csN4 lay ≤ chainCount lay := by
  unfold csN4; split_ifs with h
  · subst h; simp [chainCount]
  · omega
theorem endpoint_eq (lay : Layer) (i : Nat) : maxDigit lay i = endpoint lay i (csN4 lay) := by
  unfold maxDigit endpoint
  split_ifs <;> rfl

/-- T51: the top leaf is `end_0 | tweak | end_1 .. end_50` (endpad), the same shape as a lower leaf. -/
theorem leafInput_words' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    wordsOf (pad64 (T3.leafInput lay tree leaf ends)) =
      wordsOf (bytesLE 16 (ends.getD 0 0)) ++ [T3.hyperWord lay.val (tree * 2 ^ height lay + leaf), 0] ++
        wordsOf ((ends.drop 1).flatMap (bytesLE 16)) := by
  unfold T3.leafInput T3.leafTweak
  rw [ite_self]
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, Nat.mul_comm]
  have hal : (bytesLE 16 (ends.getD 0 0) ++ bytesLE 16 (0#64 ++ T3.hyperWord lay.val (tree * 2 ^ height lay + leaf)) ++
      (ends.drop 1).flatMap (bytesLE 16)).length % 64 = 0 := by
    simp only [List.length_append, bytesLE_length, hfl]
    rcases chainCount_cases' lay with h | h <;> rw [h]
  rw [pad64_of_aligned _ hal,
    wordsOf_append _ _ (by simp only [List.length_append, bytesLE_length] <;> omega),
    wordsOf_append _ _ (by simp only [bytesLE_length] <;> omega), wordsOf_bytesLE16 (_ ++ _),
    T3.append64_low, BitVec.extractLsb'_append_eq_left]
  rfl

def leafBlocks' (lay : Layer) : Nat := (16 * (chainCount lay + 1) + 63) / 64
theorem leafInput_length' (lay : Layer) (tree leaf : Nat) (ends : List Digest) (hlen : ends.length = chainCount lay) :
    (pad64 (T3.leafInput lay tree leaf ends)).length = 64 * leafBlocks' lay := by
  unfold T3.leafInput leafBlocks'
  rw [ite_self]
  have hfl : ((ends.drop 1).flatMap (bytesLE 16)).length = 16 * (chainCount lay - 1) := by
    rw [List.length_flatMap]; simp [bytesLE_length, hlen, Nat.mul_comm]
  rw [pad64_length]
  simp only [List.length_append, bytesLE_length, hfl]
  rcases chainCount_cases' lay with h | h <;> rw [h]

theorem leafBlocks'_cases (lay : Layer) : leafBlocks' lay = 13 ∧ chainCount lay = 51 ∨
    leafBlocks' lay = 11 ∧ chainCount lay = 43 := by
  unfold leafBlocks'; rcases chainCount_cases' lay with h | h <;> rw [h] <;> simp
def sideOff (leaf j : Nat) : Nat := if leaf / 2 ^ j % 2 = 1 then 0 else 48
def RlScratch (A : Nat) : Prop :=
  A = CHAIN + 16 ∨ A = CHAIN + 24 ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (LEAFPK ≤ A ∧ A < LEAFPK + 896) ∨
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ A = ENC ∨ A = ENC + 8 ∨ (0x66700 ≤ A ∧ A < 0x66760) ∨
  (0xA0000 ≤ A ∧ A < 0xA0768)
def RlWit (lay : Layer) (leaf WC WM : Nat) (A : Nat) : Prop :=
  (∃ i < chainCount lay, A = WC - 64 * i + 48 ∨ A = WC - 64 * i + 56) ∨
  (∃ j < height lay, A = WM - 64 * j + sideOff leaf j ∨ A = WM - 64 * j + sideOff leaf j + 8)
def rlRegs : List Reg :=
  [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x17, .x19, .x20, .x21, .x22, .x23, .x24, .x28, .x29, .x30, .x31]
structure RlPre (s : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat)
    (P WC WM ret : Nat) : Prop where
  pc : s.pc = pcOf 997
  x1 : s.getReg .x1 = pcOf ret
  x5 : s.getReg .x5 = 0
  x8 : s.getReg .x8 = BitVec.ofNat 64 lay.val
  x9 : s.getReg .x9 = BitVec.ofNat 64 (route index lay).2
  x18 : s.getReg .x18 = BitVec.ofNat 64 (route index lay).1
  x15 : s.getReg .x15 = BitVec.ofNat 64 (height lay)
  x26 : s.getReg .x26 = BitVec.ofNat 64 (chainCount lay)
  x27 : s.getReg .x27 = BitVec.ofNat 64 (csN4 lay)
  x16 : s.getReg .x16 = BitVec.ofNat 64 P
  x23 : s.getReg .x23 = BitVec.ofNat 64 WC
  x24 : s.getReg .x24 = BitVec.ofNat 64 WM
  hidx : index < 2 ^ 31
  hP : 0x7000 ≤ P
  hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616
  hP8 : P % 8 = 0
  hWC8 : WC % 8 = 0
  hWM8 : WM % 8 = 0
  hWM : 0x800 + 64 * (height lay - 1) ≤ WM
  hWMC : WM + 64 + 64 * (chainCount lay - 1) ≤ WC
  hWC : WC + 64 ≤ 0x7000
  dbytes : ∀ i < chainCount lay, s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 (digits.getD i 0)
  hdig : ∀ i < chainCount lay, digits.getD i 0 ≤ maxDigit lay i
  vals : ∀ i (h : i < chainCount lay), DigAt s (P + 16 * i) ((sig.layers lay).values ⟨i, h⟩)
  path : ∀ j (h : j < height lay), DigAt s (P + 16 * chainCount lay + 16 * j) ((sig.layers lay).path ⟨j, h⟩)
  c0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  c8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
  n32 : s.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  n40 : s.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
theorem route_lt (index : Nat) (lay : Layer) : (route index lay).1 < 2 ^ height lay := by
  unfold route; exact Nat.mod_lt _ (by positivity)
theorem route_routed (index : Nat) (lay : Layer) (h : index < 2 ^ 31) :
    (route index lay).2 * 2 ^ height lay + (route index lay).1 < 2 ^ 32 := by
  unfold route
  dsimp only
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
theorem route_tree_lt (index : Nat) (lay : Layer) (h : index < 2 ^ 31) : (route index lay).2 < 2 ^ 32 := by
  unfold route
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
def lval (sig : Signature) (lay : Layer) (i : Nat) : Digest :=
  if h : i < chainCount lay then (sig.layers lay).values ⟨i, h⟩ else 0
def lpath (sig : Signature) (lay : Layer) (j : Nat) : Digest :=
  if h : j < height lay then (sig.layers lay).path ⟨j, h⟩ else 0
theorem slotOff_lt (lay : Layer) {i n : Nat} (hi : i < n) : slotOff lay i + 16 ≤ 16 * (n + 2) := by
  unfold slotOff; split_ifs <;> omega
theorem slotOff_ne (lay : Layer) {i j : Nat} (h : i ≠ j) :
    slotOff lay i + 16 ≤ slotOff lay j ∨ slotOff lay j + 16 ≤ slotOff lay i := by
  unfold slotOff; split_ifs <;> omega
section phase
variable {sk : BitVec 256}
/-- C2 (FULL) + C4: offset of the current value in the 32-byte node output at level `j`: the high half when the
current node is a left child below the root (every layer; C4 adds the top), the low half for a right child and for
the root (`j = height lay`, heap 1). -/
def curOff (lay : Layer) (leaf j : Nat) : Nat :=
  if ClaudeWCT.WCT9.lowerHigh lay.val (leaf / 2 ^ j) && decide (j < height lay) then 16 else 0
theorem curOff_le (lay : Layer) (leaf j : Nat) : curOff lay leaf j ≤ 16 := by unfold curOff; split_ifs <;> omega
theorem curOff_bit0 (lay : Layer) {leaf j : Nat} (h : leaf / 2 ^ j % 2 = 0) (hj : j < height lay) :
    curOff lay leaf j = hiOff lay.val := by
  have hl := lay.isLt
  unfold curOff hiOff ClaudeWCT.WCT9.lowerHigh
  simp [h, hj, hl]
theorem curOff_bit1 (lay : Layer) {leaf j : Nat} (h : ¬ leaf / 2 ^ j % 2 = 0) : curOff lay leaf j = 0 := by
  unfold curOff ClaudeWCT.WCT9.lowerHigh; simp [h]
/-- C4: the root (level `height lay`) keeps the low half. -/
theorem curOff_root (lay : Layer) (leaf : Nat) : curOff lay leaf (height lay) = 0 := by
  unfold curOff; simp
theorem height_pos' (lay : Layer) : 0 < height lay := by fin_cases lay <;> decide
theorem curOff_zero (lay : Layer) (leaf : Nat) :
    curOff lay leaf 0 = if ClaudeWCT.WCT9.lowerHigh lay.val leaf then 16 else 0 := by
  unfold curOff; rw [Nat.pow_zero, Nat.div_one]; simp [height_pos' lay]
theorem digAt_half (t : MachineState) (a : BitVec 256) (B : Nat) (h12 : t.getReg .x12 = BitVec.ofNat 64 B)
    (hB : B + 32 < 2 ^ 64) (b : Bool) :
    DigAt (writeHash t a) (B + if b then 16 else 0) (ClaudeWCT.WCT9.halfOf b a) := by
  cases b
  · simpa using DigAt.writeHash_lo t a B h12 hB
  · simpa using DigAt.writeHash_hi t a B h12 hB
theorem block4_length (l r : Digest) (T : BitVec 128) : (bytesLE 16 l ++ bytesLE 16 T ++ zero16 ++ bytesLE 16 r).length = 64 := by
  simp [bytesLE_length, zero16]
theorem wordsOf_block4 (l r : Digest) (T : BitVec 128) :
    wordsOf (bytesLE 16 l ++ bytesLE 16 T ++ zero16 ++ bytesLE 16 r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, T.extractLsb' 0 64, T.extractLsb' 64 64, 0, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  rw [wordsOf_append _ _ (by simp [bytesLE_length, zero16]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, wordsOf_zero16,
    wordsOf_bytesLE16]
  rfl
def mkRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x13, .x14, .x17, .x20, .x22, .x24, .x28, .x29, .x30, .x31]
def MkW (leaf WM j : Nat) (A : Nat) : Prop :=
  A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨ A = NODE + 56 ∨
  (NOUT ≤ A ∧ A < NOUT + 32) ∨ (∃ j' < j, A = WM - 64 * j' + sideOff leaf j' ∨ A = WM - 64 * j' + sideOff leaf j' + 8) ∨
  (0x66700 ≤ A ∧ A < 0x66760)
structure MkInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM j : Nat) (value : Digest)
    (u : MachineState) : Prop where
  pc : u.pc = pcOf 1076
  x20 : u.getReg .x20 = BitVec.ofNat 64 j
  x22 : u.getReg .x22 = BitVec.ofNat 64 (P + 16 * chainCount lay + 16 * j)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (WM - 64 * j)
  hj : j ≤ height lay
  val : DigAt u (NOUT + curOff lay leaf j) value
  wit : ∀ j' < j, DigAt u (WM - 64 * j' + sideOff leaf j') (lpath sig lay j')
  regs : RegsExcept tc u mkRegs
  frame : Frame tc u (MkW leaf WM j)
theorem sideOff_le (leaf j : Nat) : sideOff leaf j ≤ 48 := by unfold sideOff; split_ifs <;> omega
theorem not_MkW_of {leaf WM j A : Nat} (hA1 : WM + 64 ≤ A) (hA2 : A < NODE ∨ NODE + 64 ≤ A)
    (hA3 : A < NOUT ∨ NOUT + 32 ≤ A) (hA4 : A < 0x66700 := by omega) : ¬ MkW leaf WM j A := by
  unfold MkW
  rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
    first | (simp only [NODE, NOUT] at h hA2 hA3; omega) | (have := sideOff_le leaf j'; omega) | omega
theorem mkW_of {leaf WM j A : Nat} (h : A = NODE ∨ A = NODE + 8 ∨ A = NODE + 16 ∨ A = NODE + 24 ∨ A = NODE + 48 ∨
    A = NODE + 56 ∨ (NOUT ≤ A ∧ A < NOUT + 32) ∨ (0x66700 ≤ A ∧ A < 0x66760)) : MkW leaf WM j A := by
  unfold MkW
  rcases h with h | h | h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
theorem mkW_wit {leaf WM j j' A : Nat} (hj : j' < j)
    (h : A = WM - 64 * j' + sideOff leaf j' ∨ A = WM - 64 * j' + sideOff leaf j' + 8) : MkW leaf WM j A := by
  unfold MkW
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', hj, h⟩)))))))
theorem frame_readWordsL {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (A : Nat) :
    ∀ m, A + 8 * m ≤ 2 ^ 64 → (∀ i < m, ¬ W (A + 8 * i)) →
      t.readWords (BitVec.ofNat 64 A) m = s.readWords (BitVec.ofNat 64 A) m
  | 0, _, _ => rfl
  | m + 1, hA, hW => by
    rw [readWords_add, readWords_add, frame_readWordsL h A m (by omega) (fun i hi => hW i (by omega)),
      readWords_one, readWords_one, h.get (by omega) (hW m (by omega))]
/-- img-v6 (topfold-v6): cycles of one top node below the root at level `j` (height `j + 1`): the node step with
the nonce search, at most `topNonceCap (j + 1) - 1` failed trials of 22 cycles each. -/
def topNodeW (j : Nat) : Nat := 123 + 22 * (T3.topNonceCap (j + 1) - 1)
/-- Cycles of the node climb (img-v6: the hook 1139 adds 4 (lower) / 6 (top root) cycles per plain node, 81 total;
the 11 top nodes below the root take `topNodeW`). -/
def climbW (lay : Layer) : Nat :=
  if lay = 0 then ((List.range' 0 11).map topNodeW).sum + 81 else height lay * 81
def rlCost (lay : Layer) : Nat := hpK lay + chainCount lay * 461 + 10 + 8 * leafBlocks' lay + 13 + climbW lay
/-- The top layer's 11 node nonces at `0x66700 + 8 k` and the leaf at `0x66758` (read by the pad writer). -/
def NoncesAt (t : MachineState) (nonces : List Nat) (leaf : Nat) : Prop :=
  nonces.length = 11 ∧ (∀ k < 11, t.getMem (BitVec.ofNat 64 (0x66700 + 8 * k)) = BitVec.ofNat 64 (nonces.getD k 0)) ∧
    t.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf
def RlPost (s0 : MachineState) (sig : Signature) (index : Nat) (lay : Layer) (WC WM ret : Nat) (root : Digest)
    (t : MachineState) : Prop :=
  t.pc = pcOf ret ∧ DigAt t ENC root ∧
    (∀ i < chainCount lay, DigAt t (WC - 64 * i + 48) (lval sig lay i)) ∧
    (∀ j < height lay, DigAt t (WM - 64 * j + sideOff (route index lay).1 j) (lpath sig lay j)) ∧
    RegsExcept s0 t rlRegs ∧ Frame s0 t (fun A => RlScratch A ∨ RlWit lay (route index lay).1 WC WM A)
/-- img-v6: one step of the top path with the node nonce search (`WCT9.topStepN`). -/
def topStepP (sig : Signature) (index : Nat) (lay : Layer) (acc : Digest × List Nat) (j : Fin (height lay)) :
    T3.M (Digest × List Nat) := do
  let other := (sig.layers lay).path j
  let pair := if (route index lay).1 / 2 ^ j.val % 2 = 0 then (acc.1, other) else (other, acc.1)
  let found ← T3.topNodeAt (j.val + 1) (2 ^ (height lay - j.val - 1) + (route index lay).1 / 2 ^ (j.val + 1))
    pair.1 pair.2
  pure (found.2, acc.2 ++ [found.1])
/-- The fold invariant of the top path with nonces: `MkInv` plus the nonces recorded so far. -/
def TopInv (tc : MachineState) (sig : Signature) (lay : Layer) (leaf P WM : Nat) (j : Nat) (acc : Digest × List Nat)
    (w : MachineState) : Prop :=
  MkInv tc sig lay leaf P WM j acc.1 w ∧ acc.2.length = j ∧
    (∀ k < j, w.getMem (BitVec.ofNat 64 (0x66700 + 8 * k)) = BitVec.ofNat 64 (acc.2.getD k 0)) ∧
    (0 < j → w.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf)
/-- img-v6: the top layer's recovery (`WCT9.topFoldN` then the root node): `((v, nonces), root)`. -/
def topProg (sig : Signature) (index : Nat) (lay : Layer) (digits : List Nat) (h11 : 11 < height lay) :
    T3.M ((Digest × List Nat) × Digest) :=
  ((List.finRange (chainCount lay)).mapM fun i => SigGolfCandidate.T3.layChain lay (route index lay).2
      (route index lay).1 i.val (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0)
      ((sig.layers lay).values i)) >>= fun ends =>
    SigGolfCandidate.T3.leafHash lay (route index lay).2 (route index lay).1 ends >>= fun value =>
    ((List.finRange (height lay)).take 11).foldlM (topStepP sig index lay) (value, []) >>= fun vn =>
    (let other := (sig.layers lay).path ⟨11, h11⟩
     let pair := if (route index lay).1 / 2 ^ 11 % 2 = 0 then (vn.1, other) else (other, vn.1)
     SigGolfCandidate.T3.nodeHash 3 lay.val (route index lay).2
       (2 ^ (height lay - 11 - 1) + (route index lay).1 / 2 ^ (11 + 1)) pair.1 pair.2) >>= fun root =>
    pure (vn, root)
/-- The top layer's last hashed block: level-11 node `v` and the stored top sibling. -/
def TopBlkG (sig : Signature) (index : Nat) (lay : Layer) (v : Digest) (t : MachineState) : Prop :=
  t.readWords (BitVec.ofNat 64 NODE) 8 =
    wordsOf (bytesLE 16 (if (route index lay).1 / 2 ^ 11 % 2 = 0 then v else lpath sig lay 11) ++
      bytesLE 16 (T3.nodeTweak 3 lay.val (route index lay).2 (2 ^ (height lay - 11 - 1) + (route index lay).1 / 2 ^ (11 + 1))) ++
      zero16 ++ bytesLE 16 (if (route index lay).1 / 2 ^ 11 % 2 = 0 then lpath sig lay 11 else v))
end phase
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC csN4)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem rl1117_continue (s : MachineState) (hpc : s.pc = pcOf 1117)
    (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12) (hc : j + 1 < hh ∨ lay = 0)
    (htopl : lay = 0 → leaf < 2 ^ hh)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t k, Steps im s k k t ∧ k ≤ 37 ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  have he := bc_remaining hj hh' h15 h20
  have hcont : BCBlocks.remaining s ≠ 0 ∨ s.getReg .x8 = 0 := by
    rcases hc with hc | hc
    · left
      rw [he]
      intro hz
      have := congrArg BitVec.toNat hz
      change (hh - j - 1) % 2 ^ 64 = 0 at this
      rw [Nat.mod_eq_of_lt (show hh - j - 1 < 2 ^ 64 by omega)] at this
      omega
    · right; rw [h8, hc]; rfl
  obtain ⟨u, k, su, hk, up, u28, ur, uf⟩ := BCBlocks.continue_spec (im := im) s hpc hcont
  obtain ⟨t, ut, tp, m16, m24, t10, t11, t12, tr, tf⟩ := rl1119_spec (im := im) u up lay tree leaf hh j
    hlay htree hl hj hh' htopl
    (by rw [ur.get (by decide)]; exact h8) (by rw [ur.get (by decide)]; exact h9)
    (by rw [ur.get (by decide)]; exact h18) (by rw [ur.get (by decide)]; exact h15)
    (by rw [ur.get (by decide)]; exact h20) (u28.trans he)
  refine ⟨t, k + hdrK lay, su.trans ut, by unfold hdrK; split_ifs <;> omega, tp, m16, m24, t10, t11, t12, ?_, ?_⟩
  · exact (ur.trans tr).mono (by decide)
  · exact (uf.trans tf).mono (by intro A hA h; simpa using h)

theorem rl_chains {s0 t1 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret)
    (r1 : RegsExcept s0 t1 [.x6, .x7, .x19, .x28, .x30])
    (f1 : Frame s0 t1 (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24))
    (hI0 : ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC (chainCount lay) (csN4 lay)
      (lval sig lay) [] t1) :
    TBSim im sk t1 (chainCount lay * 461)
      ((List.finRange (chainCount lay)).mapM fun i => ClaudeWCT.WCT9.chainW lay (route index lay).2 (route index lay).1 i.val
        (digits.getD i.val 0) (maxDigit lay i.val - digits.getD i.val 0) ((sig.layers lay).values i))
      (fun ends u => ends.length = chainCount lay ∧ ChainsInv t1 lay (route index lay).2 (route index lay).1 P WC
        (chainCount lay) (csN4 lay) (lval sig lay) ends u) := by
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hN := chainCount_cases' lay
  have hH := height_le lay
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  refine tb_mapM_finRange (chainCount lay) _ 461 _ (fun i pre t hlen hI => ?_) hI0
  have hi := i.isLt
  have hfr : Frame s0 t (fun A => (A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨ ChW lay WC pre.length A) :=
    f1.trans hI.frame
  have g : ∀ r, r ∉ oneRegs → r ∉ [Reg.x6, .x7, .x19, .x28, .x30] → t.getReg r = s0.getReg r :=
    fun r h1 h2 => by rw [hI.regs.get h1, r1.get h2]
  have h26 : t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) := by
    rw [g _ (by decide) (by decide), hpre.x26]
  have h27 : t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) := by rw [g _ (by decide) (by decide), hpre.x27]
  have h16 : t.getReg .x16 = BitVec.ofNat 64 P := by rw [g _ (by decide) (by decide), hpre.x16]
  have h23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * i.val) := by rw [hI.x23, hlen]
  have hv : DigAt t (P + 16 * i.val) ((sig.layers lay).values i) :=
    (hpre.vals i.val hi).frame hfr (by omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK] at h; omega
          · exact not_ChW_of (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega) h)
  have hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i.val)) = BitVec.ofNat 8 (digits.getD i.val 0) := by
    rw [Frame.getByte hfr (by simp only [DIGITS]; omega)
      (by rintro (h | h); · simp only [CHAIN, LEAFPK, DIGITS] at h; omega
          · exact not_ChW_of (by omega) (by simp only [DIGITS]; omega) (by simp only [CHAIN, DIGITS]; omega)
              (by simp only [LEAFPK, DIGITS]; omega) h)]
    exact hpre.dbytes i.val hi
  have hd : digits.getD i.val 0 ≤ endpoint lay i.val (csN4 lay) := by
    have := hpre.hdig i.val hi; rwa [endpoint_eq] at this
  have hc : ChainCtx lay.val tree leaf i.val t := hlen ▸ hI.ctx
  have hone := rl_one (im := im) (sk := sk) lay tree leaf i.val (digits.getD i.val 0) P (WC - 64 * i.val) (chainCount lay)
    (csN4 lay) (by
      have hidx := hpre.hidx
      dsimp [tree, leaf]
      fin_cases lay <;> norm_num [route, height] at * <;> omega)
    (route_lt index lay) hi (by omega) (fun hl => by subst hl; simp [chainCount] at hi; omega) (csN4_le lay) hpre.hP (by omega) hpre.hP8
    (by have := hpre.hWC8; omega) (by omega) (by omega) hd (le_of_eq (endpoint_eq lay i.val).symm)
    ((sig.layers lay).values i) t hI.pc hc h26 h27 h16 h23 hv
    hdig
  rw [endpoint_eq]
  refine hone.mono le_rfl (fun d u hu => ?_)
  obtain ⟨upc, u19, u23, uc, uslot, uval, ur, uf⟩ := hu
  have hl1 : (pre ++ [d]).length = i.val + 1 := by simp [hlen]
  refine ⟨upc, hl1 ▸ uc, ?_, ?_, ?_, (hI.regs.trans ur).mono (fun r hr => by
    rcases List.mem_append.mp hr with h | h <;> exact h), (hI.frame.trans uf).mono (fun A _ h => ?_)⟩
  · rw [u23, hl1, Nat.mul_succ, Nat.sub_sub]
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hs := hI.slots j (by omega)
      rw [List.getD_append _ _ _ _ (by omega)]
      have hne := slotOff_ne lay (show j ≠ i.val by omega)
      have hlt := slotOff_lt lay (show j < chainCount lay by omega)
      exact hs.frame uf (by simp only [LEAFPK]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
        (by unfold OneW StepW; simp only [LEAFPK, CHAIN]; omega)
    · rw [List.getD_append_right _ _ _ _ (by omega), show i.val - pre.length = 0 by omega]
      simpa using uslot
  · intro j hj
    rw [hl1] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have hw := hI.wvals j (by omega)
      exact hw.frame uf (by omega) (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
        (by unfold OneW StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega)
    · have : lval sig lay i.val = (sig.layers lay).values i := by unfold lval; rw [dif_pos hi]
      rw [this]
      exact uval
  · rw [hl1]
    unfold ChW
    rcases h with h | h
    · rw [hlen] at h
      rcases h with h | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
      · exact Or.inr (Or.inr ⟨c, by omega, h⟩)
    · unfold OneW at h
      rcases h with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inl ⟨i.val, by omega, Or.inr h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inl h⟩)
      · exact Or.inr (Or.inr ⟨i.val, by omega, Or.inr h⟩)
/-- C2 (FULL): offset of the current value in the 32-byte node output at level `j` (high half for lower layers when
the current node is a left child). -/

theorem rl_mk_step {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (hj : j < height lay) (hc : j + 1 < height lay ∨ lay = 0) (htree : tree < 2 ^ 32) (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) (hskip : lay ≠ 0 ∨ 11 ≤ j) :
    TBSim im sk u 81 (let other := (sig.layers lay).path ⟨j, hj⟩
        let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
        ClaudeWCT.WCT9.lowerNodeHash lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2)
      (fun v' u' => MkInv tc sig lay leaf P WM (j + 1) v' u' ∧
        u'.readWords (BitVec.ofNat 64 NODE) 8 =
          wordsOf (bytesLE 16 (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ++
            bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1))) ++
            zero16 ++ bytesLE 16 (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value)) ∧
        (∀ A, 0x66700 ≤ A → A < 0x66760 → u'.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A))) := by
  have hH := height_le lay
  have hlay := lay.isLt
  have hleaf' : leaf < 2 ^ 12 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) hH)
  have g : ∀ r, r ∉ mkRegs → u.getReg r = tc.getReg r := fun r h => hI.regs.get h
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1076_spec (im := im) u hI.pc j (height lay) (by omega) (by omega) hI.x20
    (by rw [g _ (by decide)]; exact c15)
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := rl1077_spec (im := im) t1 p1 leaf j (by omega) (by omega)
    (by rw [r1.get (by decide), g _ (by decide)]; exact c18) (by rw [r1.get (by decide)]; exact hI.x20)
  have fu2 : Frame u t2 (fun _ => False) := (f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u t2 [.x28] := (r1.trans r2).mono (by decide)
  have hpu : DigAt u (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) :=
    cpath.frame hI.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
      (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
  set P' := P + 16 * chainCount lay + 16 * j with hP'def
  set M := WM - 64 * j with hMdef
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 P' := by rw [ru2.get (by decide)]; exact hI.x22
  have h24 : t2.getReg .x24 = BitVec.ofNat 64 M := by rw [ru2.get (by decide)]; exact hI.x24
  have hco := curOff_le lay leaf j
  have hval2 : DigAt t2 (NOUT + curOff lay leaf j) value :=
    hI.val.frame fu2 (by simp only [NOUT]; omega) (by simp) (by simp)
  have hpu2 : DigAt t2 P' (lpath sig lay j) := hpu.frame fu2 (by omega) (by simp) (by simp)
  have hn32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn40]
  obtain ⟨t3, k3, s3, hk3, p3, nl, nr, wsib, r3, f3⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧ k3 ≤ 22 ∧
      t3.pc = pcOf 1117 ∧
      DigAt t3 NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t3 (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      DigAt t3 (M + sideOff leaf j) (lpath sig lay j) ∧
      RegsExcept t2 t3 [.x6, .x7, .x29, .x30] ∧
      Frame t2 t3 (fun A => A = M + sideOff leaf j ∨ A = M + sideOff leaf j + 8 ∨ A = NODE ∨ A = NODE + 8 ∨
        A = NODE + 48 ∨ A = NODE + 56) := by
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · rw [if_pos hb] at p2
      obtain ⟨t3, s3, p3, m48, m56, n0, n8, n48, n56, r3, f3⟩ := rl1099_spec (im := im) t2 p2 lay.val (by omega)
        (by rw [ru2.get (by decide), g _ (by decide)]; exact c8) P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 48 := by unfold sideOff; rw [if_neg (by omega)]
      have hc0 := curOff_bit0 lay hb hj
      refine ⟨t3, 22, s3, le_rfl, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_pos hb]; rw [hc0] at hval2; exact ⟨n0.trans hval2.1, n8.trans hval2.2⟩
      · rw [if_pos hb]; exact ⟨n48.trans hpu2.1, n56.trans hpu2.2⟩
      · rw [hso]; exact ⟨m48.trans hpu2.1, by rw [show M + 48 + 8 = M + 56 by omega]; exact m56.trans hpu2.2⟩
      · rw [hso]; exact f3
    · rw [if_neg hb] at p2
      obtain ⟨t3, s3, p3, m0, m8, n0, n8, n48, n56, r3, f3⟩ := rl1080_spec (im := im) t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 0 := by unfold sideOff; rw [if_pos (by omega)]
      have hval2 : DigAt t2 NOUT value := by
        have := hval2; rwa [curOff_bit1 lay hb, Nat.add_zero] at this
      refine ⟨t3, 19, s3, by omega, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_neg hb]; exact ⟨n0.trans hpu2.1, n8.trans hpu2.2⟩
      · rw [if_neg hb]; exact ⟨n48.trans hval2.1, n56.trans hval2.2⟩
      · rw [hso]; exact ⟨m0.trans hpu2.1, m8.trans hpu2.2⟩
      · rw [hso]; simpa using f3
  have g3' : RegsExcept tc t3 mkRegs := ((hI.regs.trans ru2).trans r3).mono (by decide)
  have g3 : ∀ r, r ∉ mkRegs → t3.getReg r = tc.getReg r := fun r h => g3'.get h
  obtain ⟨t4, k4, s4, hk4, p4, h16, h24', h10, h11, h12, r4, f4⟩ := rl1117_continue (im := im) t3 p3 lay.val tree leaf (height lay) j
    (by omega) htree (by omega) hj hH (by simpa using hc) (fun _ => hleaf)
    (by rw [g3 _ (by decide)]; exact c8) (by rw [g3 _ (by decide)]; exact c9)
    (by rw [g3 _ (by decide)]; exact c18) (by rw [g3 _ (by decide)]; exact c15)
    (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)
  set heap := 2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (height lay - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  set L := if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j with hL
  set R := if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value with hR
  have f34 : ∀ A, A < 2 ^ 64 → A ≠ NODE + 16 → A ≠ NODE + 24 → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f4.get hA (by rintro (h | h) <;> contradiction)
  have hblk4 : t4.readWords (BitVec.ofNat 64 NODE) 8 =
      wordsOf (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) := by
    rw [wordsOf_block4, readWords_eight, f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), h16, h24',
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), nl.1, nl.2,
      show NODE + 48 + 8 = NODE + 56 from rfl, nr.1, nr.2,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have hq : hashInput t4 = toQ (pad64 (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++
      zero16 ++ bytesLE 16 R)) := by
    rw [pad64_of_aligned _ (by rw [block4_length])]
    exact hashInput_toQ t4 _ 0 NODE (block4_length _ _ _) h10 (by decide) (by decide) h11 (by decide) hblk4
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NODE 64 NOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r34 : RegsExcept t2 t4 ([.x6, .x7, .x29, .x30] ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := r3.trans r4
  have h5 : t4.getReg .x5 = 0 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c5
  have hprog : (let other := (sig.layers lay).path ⟨j, hj⟩
      let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      ClaudeWCT.WCT9.lowerNodeHash lay.val tree (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2) =
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.lowerHigh lay.val heap)
        (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) >>= pure) := by
    have e : (sig.layers lay).path ⟨j, hj⟩ = lpath sig lay j := by unfold lpath; rw [dif_pos hj]
    rw [bind_pure, e]
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
    · simp only [hL, hR, hb, ↓reduceIte, hheap]; rfl
  rw [hprog]
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans s4))) (tb_halfHash_bind' (im := im) (W := 10) _ (fetch_1138 (im := im) t4 p4) h5 hv hq
    (fun a => ?_))).mono ?_ (fun _ _ h => h)
  rotate_left
  · rw [pad64_of_aligned _ (by rw [block4_length]), blocks_toQ ⟨by rw [block4_length]; omega,
      by rw [block4_length]⟩, block4_length]; omega
  have p5 : (writeHash t4 a).pc = pcOf 1139 := by rw [pc_writeHash, p4, pcOf_add4]
  have hskip' : height lay ≠ 12 ∨ 11 ≤ j := by
    rcases hskip with h | h
    · left; intro he; apply h; fin_cases lay <;> simp_all [height]
    · right; exact h
  obtain ⟨t6, k6, s6, hk6, p6, x22', x24', x20', r6, f6⟩ := skip_spec (im := im) (writeHash t4 a) p5 (height lay) j P' M
    (by omega) (by omega) (by omega) (by omega) hskip'
    (by rw [getReg_writeHash, r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c15)
    (by rw [getReg_writeHash, r34.get (by decide), ru2.get (by decide)]; exact hI.x20)
    (by rw [getReg_writeHash, r34.get (by decide)]; exact h22) (by rw [getReg_writeHash, r34.get (by decide)]; exact h24)
  have fw := Frame.writeHash t4 a NOUT h12 (by decide)
  have hd := digAt_half t4 a NOUT h12 (by decide) (ClaudeWCT.WCT9.lowerHigh lay.val heap)
  have hoff : (NOUT + if ClaudeWCT.WCT9.lowerHigh lay.val heap then 16 else 0) = NOUT + curOff lay leaf (j + 1) := by
    by_cases hlt : j + 1 < height lay
    · have hhi : ClaudeWCT.WCT9.lowerHigh lay.val heap = ClaudeWCT.WCT9.lowerHigh lay.val (leaf / 2 ^ (j + 1)) := by
        rw [hheap]; exact ClaudeWCT.WCT9.lowerHigh_heap (by omega)
      unfold curOff; rw [hhi]; simp [hlt]
    · have he : j + 1 = height lay := by omega
      have h1 : heap = 1 := by
        rw [hheap, show height lay - j - 1 = 0 by omega, Nat.pow_zero, he,
          Nat.div_eq_of_lt hleaf]
      rw [h1, ClaudeWCT.WCT9.lowerHigh_one, he, curOff_root]
      rfl
  have f36 : Frame t3 t6 (fun A => (A = NODE + 16 ∨ A = NODE + 24) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) :=
    ((f4.trans fw).trans f6).mono (fun A _ h => by rcases h with (h | h) | h; exact Or.inl h; exact Or.inr h; exact h.elim)
  have f46 : Frame t4 t6 (fun A => (NOUT ≤ A ∧ A < NOUT + 32) ∨ False) := fw.trans f6
  refine (TBSim.steps s6 (TBSim.pure ⟨⟨p6, x20', by rw [x22']; congr 1, by rw [x24', hMdef, Nat.mul_succ, Nat.sub_sub],
    by omega, by rw [← hoff]; exact hd.frame f6 (by split_ifs <;> decide) (by simp) (by simp), ?_, ?_, ?_⟩, ?_, ?_⟩)).mono
    (by omega) (fun _ _ h => h)
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · have hw := hI.wit j' hj'
      have hs1 := sideOff_le leaf j'
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * j' + sideOff leaf j' + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * j' + sideOff leaf j' := by
        unfold sideOff at hs1 hs2 ⊢; split_ifs <;> omega
      refine ((hw.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega) ?_ ?_).frame f36 (by omega) ?_ ?_
      · simp only [NODE]; omega
      · simp only [NODE]; omega
      · simp only [NODE, NOUT]; omega
      · simp only [NODE, NOUT]; omega
    · have hs2 := sideOff_le leaf j'
      exact wsib.frame f36 (by omega) (by simp only [NODE, NOUT]; omega) (by simp only [NODE, NOUT]; omega)
  · have rw0 : RegsExcept t4 (writeHash t4 a) [] := fun r _ => getReg_writeHash t4 a r
    exact (((g3'.trans r4).trans rw0).trans r6).mono (by decide)
  · have fall := ((hI.frame.trans fu2).trans f3).trans f36
    refine fall.mono (fun A _ h => ?_)
    unfold MkW at h ⊢
    rcases h with ((h | h) | h) | h
    · rcases h with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j', by omega, h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
    · exact h.elim
    · rcases h with h | h | h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, Or.inl h⟩)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, by omega, Or.inr h⟩)))))))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · rcases h with (h | h) | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · rw [frame_readWordsL f46 NODE 8 (by decide) (fun i hi h => by
      rcases h with h | h
      · simp only [NODE, NOUT] at h; omega
      · exact h)]
    simpa only [hL, hR, hheap] using hblk4
  · intro A hA1 hA2
    have fu6 := ((fu2.trans f3).trans f4).trans f46
    rw [fu6.get (by omega) (by
      have := sideOff_le leaf j
      have hMb : M ≤ WM := by rw [hMdef]; exact Nat.sub_le _ _
      intro hx; simp only [NODE, NOUT, false_or, or_false] at hx; omega)]

theorem tb_foldlM_valsW {γ : Type} {n : Nat} (f : γ → Fin n → T3.M γ) (W : Nat → Nat)
    (Inv : Nat → γ → MachineState → Prop) (B : Nat)
    (hbody : ∀ (i : Fin n) acc t, i.val < B → Inv i.val acc t → TBSim im sk t (W i.val) (f acc i) (Inv (i.val + 1))) :
    ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      k + xs.length ≤ B → Inv k acc t →
      TBSim im sk t (((List.range' k xs.length).map W).sum) (xs.foldlM f acc) (Inv (k + xs.length)) := by
  intro xs
  induction xs with
  | nil => intro k acc t _ _ ht; simpa using TBSim.pure (image := im) (sk := sk) ht
  | cons x xs ih =>
    intro k acc t hidx hB ht
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    simp only [List.length_cons] at hB
    rw [List.foldlM_cons, List.length_cons, List.range'_succ, List.map_cons, List.sum_cons]
    have h1 := hbody x acc t (by rw [hidx.1]; omega) (by rw [hidx.1]; exact ht)
    rw [hidx.1] at h1
    refine TBSim.bind h1 (fun acc' t' ht' => ?_)
    have := ih (k + 1) acc' t' (by simpa using hidx.2) (by omega) ht'
    rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this

/-- img-v6: a top node below the root (level `j < 11`, height `j + 1`) with the nonce search (hook 1139). -/
theorem rl_mk_stepN {tc : MachineState} {sig : Signature} {lay : Layer} {tree leaf P WM j : Nat}
    {value : Digest} {u : MachineState} (htop : lay = 0) (hj11 : j < 11) (hj : j < height lay) (htree : tree < 2 ^ 32)
    (hleaf : leaf < 2 ^ height lay)
    (hP0 : 0x7000 ≤ P) (hP' : P + 16 * (chainCount lay + height lay) ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hWM8 : WM % 8 = 0) (hWM : 0x800 + 64 * (height lay - 1) ≤ WM) (hWM' : WM + 64 ≤ 0x7000)
    (c5 : tc.getReg .x5 = 0) (c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val)
    (c9 : tc.getReg .x9 = BitVec.ofNat 64 tree) (c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf)
    (c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay))
    (cpath : DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j))
    (cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0) (cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (hI : MkInv tc sig lay leaf P WM j value u) :
    TBSim im sk u (topNodeW j) (let other := (sig.layers lay).path ⟨j, hj⟩
        let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
        T3.topNodeAt (j + 1) (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2)
      (fun res u' => MkInv tc sig lay leaf P WM (j + 1) res.2 u' ∧
        u'.getMem (BitVec.ofNat 64 (0x66700 + 8 * j)) = BitVec.ofNat 64 res.1 ∧
        u'.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf ∧
        (∀ A, 0x66700 ≤ A → A < 0x66760 → A ≠ 0x66758 → A ≠ 0x66700 + 8 * j →
          u'.getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A))) := by
  have hc : j + 1 < height lay ∨ lay = 0 := Or.inr htop
  have hH := height_le lay
  have hlay := lay.isLt
  have hleaf' : leaf < 2 ^ 12 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) hH)
  have g : ∀ r, r ∉ mkRegs → u.getReg r = tc.getReg r := fun r h => hI.regs.get h
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1076_spec (im := im) u hI.pc j (height lay) (by omega) (by omega) hI.x20
    (by rw [g _ (by decide)]; exact c15)
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ := rl1077_spec (im := im) t1 p1 leaf j (by omega) (by omega)
    (by rw [r1.get (by decide), g _ (by decide)]; exact c18) (by rw [r1.get (by decide)]; exact hI.x20)
  have fu2 : Frame u t2 (fun _ => False) := (f1.trans f2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u t2 [.x28] := (r1.trans r2).mono (by decide)
  have hpu : DigAt u (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) :=
    cpath.frame hI.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
      (not_MkW_of (by omega) (by simp only [NODE]; omega) (by simp only [NOUT]; omega))
  set P' := P + 16 * chainCount lay + 16 * j with hP'def
  set M := WM - 64 * j with hMdef
  have h22 : t2.getReg .x22 = BitVec.ofNat 64 P' := by rw [ru2.get (by decide)]; exact hI.x22
  have h24 : t2.getReg .x24 = BitVec.ofNat 64 M := by rw [ru2.get (by decide)]; exact hI.x24
  have hco := curOff_le lay leaf j
  have hval2 : DigAt t2 (NOUT + curOff lay leaf j) value :=
    hI.val.frame fu2 (by simp only [NOUT]; omega) (by simp) (by simp)
  have hpu2 : DigAt t2 P' (lpath sig lay j) := hpu.frame fu2 (by omega) (by simp) (by simp)
  have hn32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn32]
  have hn40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [fu2.get (by decide) (by simp), hI.frame.get (by decide)
      (by unfold MkW; simp only [NODE, NOUT]; rintro (h | h | h | h | h | h | h | ⟨j', _, h | h⟩ | h) <;>
        first | omega | (have := sideOff_le leaf j'; omega)), cn40]
  obtain ⟨t3, k3, s3, hk3, p3, nl, nr, wsib, r3, f3⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧ k3 ≤ 22 ∧
      t3.pc = pcOf 1117 ∧
      DigAt t3 NODE (if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j) ∧
      DigAt t3 (NODE + 48) (if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value) ∧
      DigAt t3 (M + sideOff leaf j) (lpath sig lay j) ∧
      RegsExcept t2 t3 [.x6, .x7, .x29, .x30] ∧
      Frame t2 t3 (fun A => A = M + sideOff leaf j ∨ A = M + sideOff leaf j + 8 ∨ A = NODE ∨ A = NODE + 8 ∨
        A = NODE + 48 ∨ A = NODE + 56) := by
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · rw [if_pos hb] at p2
      obtain ⟨t3, s3, p3, m48, m56, n0, n8, n48, n56, r3, f3⟩ := rl1099_spec (im := im) t2 p2 lay.val (by omega)
        (by rw [ru2.get (by decide), g _ (by decide)]; exact c8) P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 48 := by unfold sideOff; rw [if_neg (by omega)]
      have hc0 := curOff_bit0 lay hb hj
      refine ⟨t3, 22, s3, le_rfl, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_pos hb]; rw [hc0] at hval2; exact ⟨n0.trans hval2.1, n8.trans hval2.2⟩
      · rw [if_pos hb]; exact ⟨n48.trans hpu2.1, n56.trans hpu2.2⟩
      · rw [hso]; exact ⟨m48.trans hpu2.1, by rw [show M + 48 + 8 = M + 56 by omega]; exact m56.trans hpu2.2⟩
      · rw [hso]; exact f3
    · rw [if_neg hb] at p2
      obtain ⟨t3, s3, p3, m0, m8, n0, n8, n48, n56, r3, f3⟩ := rl1080_spec (im := im) t2 p2 P' M (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) h22 h24
      have hso : sideOff leaf j = 0 := by unfold sideOff; rw [if_pos (by omega)]
      have hval2 : DigAt t2 NOUT value := by
        have := hval2; rwa [curOff_bit1 lay hb, Nat.add_zero] at this
      refine ⟨t3, 19, s3, by omega, p3, ?_, ?_, ?_, r3, ?_⟩
      · rw [if_neg hb]; exact ⟨n0.trans hpu2.1, n8.trans hpu2.2⟩
      · rw [if_neg hb]; exact ⟨n48.trans hval2.1, n56.trans hval2.2⟩
      · rw [hso]; exact ⟨m0.trans hpu2.1, m8.trans hpu2.2⟩
      · rw [hso]; simpa using f3
  have g3' : RegsExcept tc t3 mkRegs := ((hI.regs.trans ru2).trans r3).mono (by decide)
  have g3 : ∀ r, r ∉ mkRegs → t3.getReg r = tc.getReg r := fun r h => g3'.get h
  obtain ⟨t4, k4, s4, hk4, p4, h16, h24', h10, h11, h12, r4, f4⟩ := rl1117_continue (im := im) t3 p3 lay.val tree leaf (height lay) j
    (by omega) htree (by omega) hj hH (by simpa using hc) (fun _ => hleaf)
    (by rw [g3 _ (by decide)]; exact c8) (by rw [g3 _ (by decide)]; exact c9)
    (by rw [g3 _ (by decide)]; exact c18) (by rw [g3 _ (by decide)]; exact c15)
    (by rw [r3.get (by decide), ru2.get (by decide)]; exact hI.x20)
  set heap := 2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 32 := by
    have : 2 ^ (height lay - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  set L := if leaf / 2 ^ j % 2 = 0 then value else lpath sig lay j with hL
  set R := if leaf / 2 ^ j % 2 = 0 then lpath sig lay j else value with hR
  have f34 : ∀ A, A < 2 ^ 64 → A ≠ NODE + 16 → A ≠ NODE + 24 → t4.getMem (BitVec.ofNat 64 A) = t3.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 => f4.get hA (by rintro (h | h) <;> contradiction)
  have hblk4 : t4.readWords (BitVec.ofNat 64 NODE) 8 =
      wordsOf (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R) := by
    rw [wordsOf_block4, readWords_eight, f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), h16, h24',
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide),
      f34 _ (by decide) (by decide) (by decide), nl.1, nl.2,
      show NODE + 48 + 8 = NODE + 56 from rfl, nr.1, nr.2,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32,
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have hq : hashInput t4 = toQ (pad64 (bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++
      zero16 ++ bytesLE 16 R)) := by
    rw [pad64_of_aligned _ (by rw [block4_length])]
    exact hashInput_toQ t4 _ 0 NODE (block4_length _ _ _) h10 (by decide) (by decide) h11 (by decide) hblk4
  have hv : hashArgumentsValid t4 = true :=
    hashArgs_const t4 NODE 64 NOUT h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have r34 : RegsExcept t2 t4 ([.x6, .x7, .x29, .x30] ++ [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30]) := r3.trans r4
  have h5 : t4.getReg .x5 = 0 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c5
  have hl0 : lay.val = 0 := by rw [htop]; rfl
  have hH12 : height lay = 12 := by subst htop; rfl
  have hheap1 : 1 ≤ heap := by rw [hheap]; exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
  have hheap2 : heap < 4096 := by
    have e : 2 ^ height lay = 2 ^ (j + 1) * 2 ^ (height lay - j - 1) := by rw [← Nat.pow_add]; congr 1; omega
    have hq : leaf / 2 ^ (j + 1) < 2 ^ (height lay - j - 1) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hleaf
    have hp : 2 ^ (height lay - j - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h11 : (2 : Nat) ^ 11 = 2048 := by norm_num
    rw [hheap]
    rw [h11] at hp
    generalize 2 ^ (height lay - j - 1) = X at hq hp ⊢
    generalize leaf / 2 ^ (j + 1) = Y at hq ⊢
    omega
  have hpar : leaf / 2 ^ (j + 1) % 2 = heap % 2 := by
    rw [hheap, hH12]
    obtain ⟨e, he⟩ : ∃ e, 12 - j - 1 = e + 1 := ⟨10 - j, by omega⟩
    rw [he, pow_succ]; omega
  have ht : T3.nodeTweak 3 0 0 heap = T3.nodeTweak 3 0 tree heap := by unfold T3.nodeTweak; simp
  have hin : topNodeInput heap 0 L R =
      bytesLE 16 L ++ bytesLE 16 (ClaudeWCT.WCT9.merkleTweak lay.val tree heap) ++ zero16 ++ bytesLE 16 R := by
    rw [hl0, ClaudeWCT.WCT9.merkleTweak_top]
    unfold topNodeInput
    rw [ne_nonceBytes_zero, ht]
  have hq' : hashInput t4 = toQ (pad64 (topNodeInput heap 0 L R)) := by rw [hin]; exact hq
  obtain ⟨w16, w24⟩ := merkleTweak_words_top tree heap hheap1 hheap2
  have hn32' : t4.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [f34 _ (by decide) (by decide) (by decide),
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn32]
  have hn40' : t4.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [f34 _ (by decide) (by decide) (by decide),
      f3.get (by decide) (by simp only [NODE]; have := sideOff_le leaf j; omega), hn40]
  have F : NFacts t4 heap leaf j P' M L R := {
    x5 := h5
    x12 := h12
    x15 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide), c15, hH12]
    x18 := by rw [r34.get (by decide), ru2.get (by decide), g _ (by decide)]; exact c18
    x20 := by rw [r34.get (by decide), ru2.get (by decide)]; exact hI.x20
    x22 := by rw [r34.get (by decide)]; exact h22
    x24 := by rw [r34.get (by decide)]; exact h24
    w0 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nl.1
    w8 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nl.2
    w16 := by rw [h16, hl0]; exact w16
    w24 := by rw [h24', hl0]; exact w24
    w32 := hn32'
    w40 := hn40'
    w48 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nr.1
    w56 := by rw [f34 _ (by decide) (by decide) (by decide)]; exact nr.2
    h1 := hheap1
    h2 := hheap2
    hj := hj11
    hpar := hpar
    hl := by omega
    hM := by rw [hMdef]; omega
    hM' := by omega }
  have e : (sig.layers lay).path ⟨j, hj⟩ = lpath sig lay j := by unfold lpath; rw [dif_pos hj]
  have hprog : (let other := (sig.layers lay).path ⟨j, hj⟩
      let pair := if leaf / 2 ^ j % 2 = 0 then (value, other) else (other, value)
      T3.topNodeAt (j + 1) (2 ^ (height lay - j - 1) + leaf / 2 ^ (j + 1)) pair.1 pair.2) =
      T3.publicHash (topNodeInput heap 0 L R) >>= fun a =>
        neTrialTail (j + 1) heap L R (topNonceCap (j + 1) - 1) 0 (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
    rw [e]
    unfold T3.topNodeAt
    rw [ne_topNonceSearch_eq, ne_topNodeHashN_bind]
    by_cases hb : leaf / 2 ^ j % 2 = 0
    · (simp only [hL, hR, hb, ↓reduceIte, hheap]) <;> rfl
    · (simp only [hL, hR, hb, ↓reduceIte, hheap]) <;> rfl
  rw [hprog]
  refine (TBSim.steps (s1.trans (s2.trans (s3.trans s4))) (ne_tb_publicHash_bind (fetch_1138 (im := im) t4 p4) h5 hv hq'
    (W := 32 + (22 * (topNonceCap (j + 1) - 1) + 20))
    (fun a => (nonce_run (im := im) sk F p4 a).mono le_rfl (fun res w hw => ?_)))).mono
    (by rw [ne_topNodeInput_blocks] <;> unfold topNodeW <;> omega) (fun _ _ h => h)
  have fw : Frame t3 w (fun A => (A = NODE + 16 ∨ A = NODE + 24) ∨ NExitW j A) := f4.trans hw.frame
  have hco : NOUT + 16 - 16 * (heap % 2) = NOUT + curOff lay leaf (j + 1) := by
    unfold curOff ClaudeWCT.WCT9.lowerHigh
    rw [hl0, hH12, ← hpar]
    rcases Nat.mod_two_eq_zero_or_one (leaf / 2 ^ (j + 1)) with hb | hb <;>
      simp [hb, show j + 1 < 12 by omega]
  have hnx : ∀ A, A < 0x7000 → ¬ ((A = NODE + 16 ∨ A = NODE + 24) ∨ NExitW j A) := by
    intro A hA h; unfold NExitW at h; simp only [NODE, NOUT] at h; omega
  refine ⟨⟨hw.pc, hw.x20, by rw [hw.x22]; congr 1, by rw [hw.x24, hMdef, Nat.mul_succ, Nat.sub_sub],
    by omega, by rw [← hco]; exact hw.out, ?_, ?_, ?_⟩, hw.nonceAt, hw.leafAt, ?_⟩
  · intro j' hj'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj' | rfl
    · have hw' := hI.wit j' hj'
      have hs1 := sideOff_le leaf j'
      have hs2 := sideOff_le leaf j
      have hne : WM - 64 * j' + sideOff leaf j' + 16 ≤ M + sideOff leaf j ∨ M + 64 ≤ WM - 64 * j' + sideOff leaf j' := by
        unfold sideOff at hs1 hs2 ⊢; split_ifs <;> omega
      refine ((hw'.frame fu2 (by omega) (by simp) (by simp)).frame f3 (by omega) ?_ ?_).frame fw (by omega)
        (hnx _ (by omega)) (hnx _ (by omega))
      · simp only [NODE]; omega
      · simp only [NODE]; omega
    · have hs2 := sideOff_le leaf j'
      exact wsib.frame fw (by omega) (hnx _ (by omega)) (hnx _ (by omega))
  · exact ((g3'.trans r4).trans hw.regs).mono (by decide)
  · refine (((hI.frame.trans fu2).trans f3).trans fw).mono (fun A _ h => ?_)
    rcases h with ((h | h) | h) | h
    · unfold MkW at h
      rcases h with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      all_goals first
        | exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
        | exact mkW_of (by omega)
        | exact mkW_wit (by omega : j' < j + 1) h
    · exact h.elim
    · rcases h with h | h | h | h | h | h
      · exact mkW_wit (by omega : j < j + 1) (Or.inl h)
      · exact mkW_wit (by omega : j < j + 1) (Or.inr h)
      all_goals exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
    · unfold NExitW at h
      exact mkW_of (by simp only [NODE, NOUT] at h ⊢; omega)
  · intro A h1 h2 h3 h4
    have fall := (fu2.trans f3).trans fw
    rw [fall.get (by omega) (by
      have := sideOff_le leaf j
      have hMb : M ≤ WM := by rw [hMdef]; exact Nat.sub_le _ _
      unfold NExitW; intro hx; simp only [NODE, NOUT, false_or, or_false] at hx; omega)]

theorem recoverTop_tbsim {s0 : MachineState} {sig : Signature} {index : Nat} {lay : Layer} {digits : List Nat}
    {P WC WM ret : Nat} (hpre : RlPre s0 sig index lay digits P WC WM ret) (htop : lay = 0) (hT11 : 11 < height lay) :
    TBSim im sk s0 (rlCost lay) (topProg sig index lay digits hT11)
      (fun r t => RlPost s0 sig index lay WC WM ret r.2 t ∧ TopBlkG sig index lay r.1.1 t ∧
        NoncesAt t r.1.2 (route index lay).1) := by
  set tree := (route index lay).2 with htree_def
  set leaf := (route index lay).1 with hleaf_def
  have htree : tree < 2 ^ 32 := route_tree_lt index lay hpre.hidx
  have hleaf : leaf < 2 ^ height lay := route_lt index lay
  have hH := height_le lay
  have hleaf32 : leaf < 2 ^ 32 := lt_of_lt_of_le hleaf (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hN := chainCount_cases' lay
  have hlay := lay.isLt
  have hPb := hpre.hP'
  have hWC := hpre.hWC
  have hWMC := hpre.hWMC
  have hWM := hpre.hWM
  have hP0 := hpre.hP
  obtain ⟨t1, st1, p1, x19, l16, l24, -, r1, f1⟩ := rl997_spec (im := im) s0 hpre.pc lay tree leaf
    (by have hidx := hpre.hidx; dsimp [tree, leaf]; fin_cases lay <;> norm_num [route, height] at * <;> omega)
    hpre.x8 hpre.x9 hpre.x18 hpre.x15
  have f1g : ∀ A, A < 2 ^ 64 → A ≠ LEAFPK → A ≠ LEAFPK + 8 → A ≠ LEAFPK + 16 → A ≠ LEAFPK + 24 →
      t1.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
    fun A hA h1 h2 h3 h4 => f1.get hA (by rintro (h | h | h | h) <;> contradiction)
  have hI0 : ChainsInv t1 lay tree leaf P WC (chainCount lay) (csN4 lay) (lval sig lay) [] t1 := by
    refine ⟨p1, ⟨?_, ?_, ?_, ?_, x19, ?_, ?_⟩, ?_, fun j hj => absurd hj (by simp), fun j hj => absurd hj (by simp),
      RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [r1.get (by decide), hpre.x5]
    · rw [r1.get (by decide), hpre.x8]
    · rw [r1.get (by decide), hpre.x9]
    · rw [r1.get (by decide), hpre.x18]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide) (by decide), hpre.c0]
    · rw [f1g _ (by decide) (by decide) (by decide) (by decide) (by decide), hpre.c8]
    · rw [r1.get (by decide), hpre.x23]; simp
  have hH12 : height lay = 11 + 1 := by subst htop; rfl
  have hl0 : lay.val = 0 := by rw [htop]; rfl
  unfold topProg
  have htr0 : (route index lay).2 = 0 := by rw [htop]; exact Nat.div_eq_of_lt hpre.hidx
  have hchW : ∀ (lf i d c : Nat) (v : Digest), SigGolfCandidate.T3.layChain lay (route index lay).2 lf i d c v =
      ClaudeWCT.WCT9.chainW lay (route index lay).2 lf i d c v := fun lf i d c v => by
    rw [htr0, htop, SigGolfCandidate.T3.layChain_top, ClaudeWCT.WCT9.chainW_top_eq]
  have hnW : ∀ (tr heap : Nat) (l r : Digest), SigGolfCandidate.T3.nodeHash 3 lay.val tr heap l r =
      ClaudeWCT.WCT9.lowerNodeHash lay.val tr heap l r := fun tr heap l r => by
    rw [hl0, ClaudeWCT.WCT9.lowerNodeHash_top]
  simp only [hchW, hnW]
  refine (TBSim.steps st1 (TBSim.bind (W₂ := 10 + 8 * leafBlocks' lay + 13 + climbW lay)
    (rl_chains (im := im) (sk := sk) hpre r1 f1 hI0) (fun ends u hu => ?_))).mono (by unfold rlCost; omega) (fun _ _ h => h)
  obtain ⟨hlen, hC⟩ := hu
  have hN58 : chainCount lay ≤ 58 := by omega
  obtain ⟨v1, sv1, pv1, rv1, fv1⟩ := rl1010_spec (im := im) u hC.pc (chainCount lay) (chainCount lay) (by omega) (by omega)
    (by rw [hC.ctx.x19, hlen]) (by rw [hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  rw [if_pos (le_refl _)] at pv1
  obtain ⟨v2, sv2, pv2, h10, h11, h12, rv2, fv2⟩ := rl1063_spec (im := im) v1 pv1 (chainCount lay) (by omega)
    (by rw [rv1.get (by decide), hC.regs.get (by decide), r1.get (by decide)]; exact hpre.x26)
  have fu2 : Frame u v2 (fun _ => False) := (fv1.trans fv2).mono (fun A _ h => by rcases h with h | h <;> exact h)
  have ru2 : RegsExcept u v2 [.x6, .x10, .x11, .x12] := (rv1.trans rv2).mono (by decide)
  have fs2 : Frame s0 v2 (fun A => ((A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨
      ChW lay WC ends.length A) ∨ False) := (f1.trans hC.frame).trans fu2
  have hhd16 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ height lay + leaf) := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inl rfl) (by omega)), l16]
  have hhd24 : v2.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 := by
    rw [fu2.get (by decide) (by simp), hC.frame.get (by decide) (not_ChW_hdr (by simp only [LEAFPK]; omega)
      (Or.inr rfl) (by omega)), l24]
  -- T51 endpad: `end_0 | tweak | end_1 .. end_50` (the top slots are the lower ones).
  have hw : v2.readWords (BitVec.ofNat 64 LEAFPK) (8 * leafBlocks' lay) =
      wordsOf (pad64 (T3.leafInput lay tree leaf ends)) := by
    rw [leafInput_words' lay tree leaf ends hlen]
    have h0 : DigAt v2 LEAFPK (ends.getD 0 0) := by
      have := (hC.slots 0 (by omega)).frame fu2 (by simp only [slotOff]; decide) (by simp) (by simp)
      simpa [slotOff] using this
    have hrest : DigsAt v2 (LEAFPK + 32) (ends.drop 1) := by
      intro c hc
      simp only [List.length_drop] at hc
      have := (hC.slots (c + 1) (by omega)).frame fu2 (by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega)
        (by simp) (by simp)
      simp only [slotOff, if_neg (show c + 1 ≠ 0 by omega)] at this
      rw [show LEAFPK + 32 + 16 * c = LEAFPK + (16 * (c + 1) + 16) by ring]
      simpa [List.getD_eq_getElem?_getD, List.getElem?_drop] using this
    have hhd : v2.readWords (BitVec.ofNat 64 (LEAFPK + 16)) 2 =
        [T3.hyperWord lay.val (tree * 2 ^ height lay + leaf), 0] := by
      rw [readWords_two, hhd16, show LEAFPK + 16 + 8 = LEAFPK + 24 from rfl, hhd24]
    have hb : 8 * leafBlocks' lay = 2 + (2 + 2 * (ends.drop 1).length) := by
      have hn51 : chainCount lay = 51 := by rw [htop]; rfl
      simp only [List.length_drop, hlen, leafBlocks', hn51]
    rw [hb, readWords_add, readWords_add, h0.words, hhd, hrest.words]
    simp only [List.append_assoc]
  have hl := leafInput_length' lay tree leaf ends hlen
  have hB : 1 ≤ leafBlocks' lay := by rcases leafBlocks'_cases lay with h | h <;> omega
  have h11' : v2.getReg .x11 = BitVec.ofNat 64 (64 * leafBlocks' lay) := by
    rw [h11]; unfold leafBlocks'; congr 1; omega
  have hq : hashInput v2 = toQ (pad64 (T3.leafInput lay tree leaf ends)) := by
    refine hashInput_toQ v2 _ (leafBlocks' lay - 1) LEAFPK (by rw [hl]; congr 1; omega) h10 (by decide) (by decide)
      (by rw [h11']; congr 2; omega) (by rcases leafBlocks'_cases lay with h | h <;> omega)
      (by rw [show 8 * (leafBlocks' lay - 1 + 1) = 8 * leafBlocks' lay by omega]; exact hw)
  have hblk : (toQ (pad64 (T3.leafInput lay tree leaf ends))).blocks = leafBlocks' lay := by
    rw [blocks_toQ ⟨by rw [hl]; omega, by rw [hl]; omega⟩, hl]; omega
  have hv : hashArgumentsValid v2 = true :=
    hashArgs_const v2 LEAFPK (64 * leafBlocks' lay) NOUT h10 h11' h12 (by decide)
      (by rcases leafBlocks'_cases lay with h | h <;> omega) (by rcases leafBlocks'_cases lay with h | h <;>
        simp only [LEAFPK] <;> omega) (by decide) (by decide)
  have rs2 : RegsExcept s0 v2 oneRegs := ((r1.trans hC.regs).trans ru2).mono (by decide)
  have h5 : v2.getReg .x5 = 0 := by rw [rs2.get (by decide), hpre.x5]
  unfold leafHash
  rw [← ClaudeWCT.WCT9.halfHash_eq_projHash]
  refine (TBSim.steps (sv1.trans sv2) (tb_halfHash_bind' (im := im) (W := 13 + climbW lay) _ (fetch_1072 (im := im) v2 pv2) h5 hv hq
    (fun a => ?_))).mono (by rw [hblk]; omega) (fun _ _ h => h)
  set tc := writeHash v2 a with htc
  have pc3 : tc.pc = pcOf 1073 := by rw [htc, pc_writeHash, pv2, pcOf_add4]
  have rtc : RegsExcept s0 tc oneRegs := fun r hr => by rw [htc, getReg_writeHash]; exact rs2 r hr
  have fwc := Frame.writeHash v2 a NOUT h12 (by decide)
  have ftc : Frame s0 tc (fun A => (((A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) ∨
      ChW lay WC ends.length A) ∨
      False) ∨ (NOUT ≤ A ∧ A < NOUT + 32)) := fs2.trans fwc
  have hfar' : ∀ A, A < 2 ^ 64 → WC + 64 ≤ A → (A < CHAIN ∨ CHAIN + 112 ≤ A) → (A < LEAFPK ∨ LEAFPK + 960 ≤ A) →
      (A < NOUT ∨ NOUT + 32 ≤ A) → tc.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    refine ftc.get hA ?_
    rintro (((h | h) | h) | h)
    · simp only [CHAIN, LEAFPK] at h h2 h3; omega
    · exact not_ChW_of (by omega) h1 (by simp only [CHAIN] at h2 ⊢; omega) (by simp only [LEAFPK] at h3 ⊢; omega) h
    · exact h
    · simp only [NOUT] at h h4; omega
  obtain ⟨v4, sv4, pv4, x20, x22, rv4, fv4⟩ := rl1073_spec (im := im) tc pc3 P (chainCount lay) (by omega)
    (by rw [rtc.get (by decide), hpre.x16]) (by rw [rtc.get (by decide), hpre.x26])
  have hM0 : MkInv tc sig lay leaf P WM 0 (ClaudeWCT.WCT9.halfOf (T3.leafHalfHigh lay leaf) a) v4 := by
    refine ⟨pv4, x20, by rw [x22]; congr 1, ?_, by omega, ?_, fun j hj => absurd hj (by omega), rv4.mono (by decide),
      fv4.mono (fun _ _ h => h.elim)⟩
    · rw [rv4.get (by decide), rtc.get (by decide), hpre.x24]; congr 1
    · have hlh : T3.leafHalfHigh lay leaf = ClaudeWCT.WCT9.lowerHigh lay.val leaf := by
        rw [htop, ← ClaudeWCT.WCT9.lowerHigh_top_eq_leafHalfHigh]
      rw [curOff_zero, hlh]
      exact (digAt_half v2 a NOUT h12 (by decide) _).frame fv4 (by split_ifs <;> decide) (by simp) (by simp)
  have c5 : tc.getReg .x5 = 0 := by rw [rtc.get (by decide), hpre.x5]
  have c8 : tc.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [rtc.get (by decide), hpre.x8]
  have c9 : tc.getReg .x9 = BitVec.ofNat 64 tree := by rw [rtc.get (by decide), hpre.x9]
  have c18 : tc.getReg .x18 = BitVec.ofNat 64 leaf := by rw [rtc.get (by decide), hpre.x18]
  have c15 : tc.getReg .x15 = BitVec.ofNat 64 (height lay) := by rw [rtc.get (by decide), hpre.x15]
  have cn32 : tc.getMem (BitVec.ofNat 64 (NODE + 32)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n32]
  have cn40 : tc.getMem (BitVec.ofNat 64 (NODE + 40)) = 0 := by
    rw [hfar' _ (by decide) (by simp only [NODE]; omega) (by simp only [NODE, CHAIN]; omega)
      (by simp only [NODE, LEAFPK]; omega) (by simp only [NODE, NOUT]; omega), hpre.n40]
  have cpath : ∀ j < height lay, DigAt tc (P + 16 * chainCount lay + 16 * j) (lpath sig lay j) := by
    intro j hj
    have hp := hpre.path j hj
    have e : lpath sig lay j = (sig.layers lay).path ⟨j, hj⟩ := by unfold lpath; rw [dif_pos hj]
    rw [e]
    exact ⟨(hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega) (by simp only [LEAFPK]; omega)
      (by simp only [NOUT]; omega)).trans hp.1, (hfar' _ (by omega) (by omega) (by simp only [CHAIN]; omega)
      (by simp only [LEAFPK]; omega) (by simp only [NOUT]; omega)).trans hp.2⟩
  have hmap : ((List.finRange (height lay)).take 11).map Fin.val =
      List.range' 0 ((List.finRange (height lay)).take 11).length := by subst htop; decide
  have hlen11 : ((List.finRange (height lay)).take 11).length = 11 := by subst htop; decide
  have hbody : ∀ (i : Fin (height lay)) (acc : Digest × List Nat) (w : MachineState), i.val < 11 →
      TopInv tc sig lay leaf P WM i.val acc w →
      TBSim im sk w (topNodeW i.val) (topStepP sig index lay acc i) (TopInv tc sig lay leaf P WM (i.val + 1)) := by
    intro i acc w hi hw
    obtain ⟨hI, hlen, hn, hlf⟩ := hw
    have e : topStepP sig index lay acc i = (T3.topNodeAt (i.val + 1)
        (2 ^ (height lay - i.val - 1) + leaf / 2 ^ (i.val + 1))
        (if leaf / 2 ^ i.val % 2 = 0 then (acc.1, (sig.layers lay).path ⟨i.val, i.isLt⟩)
          else ((sig.layers lay).path ⟨i.val, i.isLt⟩, acc.1)).1
        (if leaf / 2 ^ i.val % 2 = 0 then (acc.1, (sig.layers lay).path ⟨i.val, i.isLt⟩)
          else ((sig.layers lay).path ⟨i.val, i.isLt⟩, acc.1)).2 >>= fun found =>
        pure (found.2, acc.2 ++ [found.1])) := rfl
    rw [e]
    refine (TBSim.bind (W₂ := 0) (rl_mk_stepN (im := im) (sk := sk) htop hi i.isLt htree hleaf hpre.hP hpre.hP'
      hpre.hP8 hpre.hWM8 hpre.hWM (by omega) c5 c8 c9 c18 c15 (cpath i.val i.isLt) cn32 cn40 hI)
      (fun res w' h => TBSim.pure ⟨h.1, ?_, ?_, ?_⟩)).mono (by omega) (fun _ _ h => h)
    · simp [hlen]
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · rw [h.2.2.2 (0x66700 + 8 * k) (by omega) (by omega) (by omega) (by omega), hn k hk,
          List.getD_append _ _ _ _ (by omega)]
      · rw [h.2.1, List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self] <;> rfl
    · intro _; exact h.2.2.1
  have hfold := tb_foldlM_valsW (im := im) (sk := sk) (topStepP sig index lay) topNodeW
    (TopInv tc sig lay leaf P WM) 11 hbody
    ((List.finRange (height lay)).take 11) 0 (ClaudeWCT.WCT9.halfOf (T3.leafHalfHigh lay leaf) a, []) v4 hmap
    (by rw [hlen11]) ⟨hM0, rfl, fun k hk => absurd hk (by omega), fun h => absurd h (by omega)⟩
  rw [hlen11] at hfold
  refine (TBSim.steps sv4 (TBSim.bind (W₂ := 81 + 10) hfold (fun vn w0 hw0 => ?_))).mono
    (by unfold climbW; rw [if_pos htop]; omega) (fun _ _ h => h)
  obtain ⟨hw0, hlen0, hn0, hlf0⟩ := hw0
  refine (TBSim.bind (W₂ := 10) (rl_mk_step (im := im) hT11 (Or.inr htop) htree hleaf hpre.hP hpre.hP' hpre.hP8 hpre.hWM8 hpre.hWM
      (by omega) c5 c8 c9 c18 c15 (cpath 11 hT11) cn32 cn40 (by simpa using hw0) (Or.inr le_rfl)) (fun root w hw' => ?_)).mono
    (by omega) (fun _ _ h => h)
  obtain ⟨hw, hblkw, hkeep⟩ := hw'
  rw [show (11 + 1 : Nat) = height lay from hH12.symm] at hw
  obtain ⟨wx1, swx1, pwx1, rwx1, fwx1⟩ := rl1076_spec (im := im) w hw.pc (height lay) (height lay) (by omega) (by omega)
    hw.x20 (by rw [hw.regs.get (by decide)]; exact c15)
  rw [if_pos (le_refl _)] at pwx1
  have rsw : RegsExcept s0 wx1 rlRegs := ((rtc.trans hw.regs).trans rwx1).mono (by decide)
  obtain ⟨t, st, pt, e0, e8, rt, ft⟩ := rl1143_spec (im := im) wx1 pwx1 ret (by rw [rsw.get (by decide), hpre.x1])
  have fw1 : Frame w wx1 (fun _ => False) := fwx1
  refine TBSim.steps (swx1.trans st) (TBSim.pure ⟨⟨pt, ?_, ?_, ?_, ((rsw.trans rt).mono (by decide)), ?_⟩, ?_, ?_⟩)
  · have hv0 := hw.val
    rw [curOff_root, Nat.add_zero] at hv0
    refine ⟨e0.trans ?_, e8.trans ?_⟩
    · rw [fw1.get (by decide) (by simp)]; exact hv0.1
    · rw [fw1.get (by decide) (by simp)]; exact hv0.2
  · intro i hi
    have hv := hC.wvals i (by omega)
    have hWi : WM + 64 ≤ WC - 64 * i + 48 := by omega
    refine (((hv.frame fu2 (by omega) (by simp) (by simp)).frame fwc (by omega) (by simp only [NOUT]; omega)
      (by simp only [NOUT]; omega)).frame hw.frame (by omega) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega)) (not_MkW_of (by omega) (by simp only [NODE]; omega)
      (by simp only [NOUT]; omega))).frame (fw1.trans ft) (by omega) ?_ ?_
    · rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
    · rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega)
  · intro j hj
    have hs := sideOff_le leaf j
    exact (hw.wit j hj).frame (fw1.trans ft) (by omega)
      (by rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
      (by rintro (h | h | h) <;> first | exact h | (simp only [ENC] at h; omega))
  · have fall := ((ftc.trans hw.frame).trans fw1).trans ft
    refine fall.mono (fun A _ h => ?_)
    unfold RlScratch RlWit
    rcases h with ((((((hX | hC) | hF) | hN) | hM) | hF2) | hE)
    · rcases hX with h | h | h | h <;>
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
    · unfold ChW StepW at hC
      rcases hC with (h | h) | ⟨c, hc, h⟩ | ⟨c, hc, h⟩
      · exact Or.inl (by rcases h with h | h; exact Or.inl h; exact Or.inr (Or.inl h))
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · have hlt := slotOff_lt lay (show c < chainCount lay by omega)
        exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (by simp only [LEAFPK] at h ⊢; omega)))))
      · exact Or.inr (Or.inl ⟨c, by omega, h⟩)
    · exact hF.elim
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl hN)))))))))))
    · unfold MkW at hM
      rcases hM with h | h | h | h | h | h | h | ⟨j', hj', h⟩ | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h)))))))))))
      · exact Or.inr (Or.inr ⟨j', hj', h⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))))))
    · exact hF2.elim
    · rcases hE with h | h
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h))))))))))))
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h)))))))))))))
  · unfold TopBlkG
    rw [frame_readWordsL (fw1.trans ft) NODE 8 (by decide) (fun i hi h => by
      rcases h with h | h | h
      · exact h
      · simp only [NODE, ENC] at h; omega
      · simp only [NODE, ENC] at h; omega)]
    rw [hblkw, hl0, ClaudeWCT.WCT9.merkleTweak_top]
  · have fwt : Frame w t (fun A => False ∨ (A = ENC ∨ A = ENC + 8)) := fw1.trans ft
    have hkt : ∀ A, 0x66700 ≤ A → A < 0x66760 → t.getMem (BitVec.ofNat 64 A) = w0.getMem (BitVec.ofNat 64 A) :=
      fun A h1 h2 => by rw [fwt.get (by omega) (by intro hx; simp only [ENC, false_or] at hx; omega), hkeep A h1 h2]
    refine ⟨by simpa using hlen0, fun k hk => ?_, ?_⟩
    · rw [hkt (0x66700 + 8 * k) (by omega) (by omega)]; exact hn0 k (by omega)
    · rw [hkt 0x66758 (by omega) (by omega)]; exact hlf0 (by omega)


end SigGolfCandidate.T3M.Expand.SharedRecover
end
