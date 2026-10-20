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
sym_block nbD := symRun { noAlias := true } nonce_D (pcOf 43204) 30
sym_block nbE := symRun { noAlias := true } nonce_E (pcOf 43207) 30
sym_block nbF := symRun { noAlias := true } nonce_F (pcOf 43213) 30
sym_block nbG := symRun { noAlias := true } nonce_G (pcOf 43215) 30
sym_block nbL := symRun { noAlias := true } nonce_L (pcOf 43225) 30
sym_block nbH := symRun { noAlias := true } nonce_H (pcOf 43228) 30
sym_block nbI := symRun { noAlias := true } nonce_I (pcOf 43232) 30
sym_block nbJ := symRun { noAlias := true } nonce_J (pcOf 43239) 30
sym_block nbK := symRun { noAlias := true } nonce_K (pcOf 43240) 30
sym_block nbS := symRun { noAlias := true } nonce_S (pcOf 43248) 30

/-- Mask of the zero test on the high word of a top node of height `h` (`1 ≤ h ≤ 11`). -/
def maskE (h : Nat) : Nat := if h = 11 then (2 ^ 11 - 1) * 2 ^ 34 else (2 ^ h - 1) * 2 ^ (64 - h)
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

theorem nC_spec (hpc : s.pc = pcOf 43199) (j : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 43204 ∧ t.getReg .x13 = BitVec.ofNat 64 (j + 1) ∧
      t.getReg .x14 = BitVec.ofNat 64 (j + 1) ∧ RegsExcept s t [.x13, .x14, .x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbC (Code.codeAt_nC (im := im)) s hpc (by simp [nbC.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [nbC.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbC.res, rv_simp, h20]; rw [ofNat_add_ofNat]
  · simp only [Result.toState_getReg, nbC.res, rv_simp, h20]; rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [nbC.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbC.res, rv_simp]

theorem nD_spec (hpc : s.pc = pcOf 43204) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 43207 ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbD (Code.codeAt_nD (im := im)) s hpc (by simp [nbD.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [nbD.res, Result.toState_pc, E.eval]
  · intro r hr; simp at hr; cases r <;> simp_all [nbD.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbD.res, rv_simp]

theorem nE_spec (hpc : s.pc = pcOf 43207) (b h : Nat) (hb : 1 ≤ b) (hb' : b ≤ 11)
    (hh : h < 2 ^ 64) (h14 : s.getReg .x14 = BitVec.ofNat 64 b) (h13 : s.getReg .x13 = BitVec.ofNat 64 h) :
    ∃ t, Steps im s 6 6 t ∧ t.pc = (if h = 11 then pcOf 43213 else pcOf 43215) ∧
      t.getReg .x31 = BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) ∧
      RegsExcept s t [.x28, .x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbE (Code.codeAt_nE (im := im)) s hpc (by simp [nbE.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, nbE.res, E.eval, CmpOp.eval, RegFile.get, h13]
    by_cases hc : h = 11
    · subst hc; simp
    · have : BitVec.ofNat 64 h ≠ BitVec.ofNat 64 11 := by rw [Ne, ofNat_inj hh (by norm_num)]; exact hc
      simp [hc, this]
  · simp only [Result.toState_getReg, nbE.res, rv_simp, h14]
    interval_cases b <;> decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbE.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbE.res, rv_simp]

theorem nF_spec (hpc : s.pc = pcOf 43213) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 43215 ∧ t.getReg .x31 = BitVec.ofNat 64 ((2 ^ 11 - 1) * 2 ^ 34) ∧
      RegsExcept s t [.x31] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbF (Code.codeAt_nF (im := im)) s hpc (by simp [nbF.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [nbF.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbF.res, rv_simp]; decide
  · intro r hr; simp at hr; cases r <;> simp_all [nbF.res, rv_simp] <;> rfl
  · intro A _ _; simp [nbF.res, rv_simp]

theorem nG_spec (hpc : s.pc = pcOf 43215) (h leaf : Nat) (hh : h ≤ 11) (hl : leaf < 2 ^ 64)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 h) (h14 : s.getReg .x14 = BitVec.ofNat 64 h)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 43225 ∧ t.getReg .x17 = BitVec.ofNat 64 (104 * 2 ^ h) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (leaf / 2 ^ h % 2)) ∧
      RegsExcept s t [.x17, .x29, .x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound nbG (Code.codeAt_nG (im := im)) s hpc (by simp [nbG.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [nbG.res, Result.toState_pc, E.eval]
  · simp only [Result.toState_getReg, nbG.res, rv_simp, h14]
    interval_cases h <;> decide
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
