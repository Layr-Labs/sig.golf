import SigGolfCandidate.T3M_Keygen_PackedShared
import SigGolfCandidate.T3M_Keygen_PackedInput

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
def kG : List (BitVec 32) := [0x010e3303, 0x046e3023, 0x018e3303, 0x046e3423, 0x040e3823, 0x040e3c23, 0x060e3023,
  0x060e3423, 0x030e0513, 0x04000593, 0x020e0613, 0x00300313, 0x03300393, 0x0079c463]
def kG9 : List (BitVec 32) := [0x00600313]
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

theorem kmd (i : Nat) : maxDigit 0 i = if i < 51 then 4 else 7 := by simp [maxDigit]
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
`addi; jal` tail at 141): G `23 + [i ≥ 51] + [terminal]`, F (odd chain) `11`. -/
def kgX (i m : Nat) : Nat :=
  if topIsG i then 23 + (if 51 ≤ i then 1 else 0) + (if m + 1 = maxDigit 0 i then 1 else 0) else 11

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

/-- The G body 695..711: header copy, pads, HASH arguments (output `CHAIN+48` on the terminal step). -/
theorem kg_spec (s : MachineState) (hpc : s.pc = pcOf 695) (i m : Nat) (hi : i < 2 ^ 63) (hm : m < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h20 : s.getReg .x20 = BitVec.ofNat 64 m)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps Images.keygenImage s (15 + (if 51 ≤ i then 1 else 0) + (if m + 1 = maxDigit 0 i then 1 else 0))
        (15 + (if 51 ≤ i then 1 else 0) + (if m + 1 = maxDigit 0 i then 1 else 0)) t ∧ t.pc = pcOf 712 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m + 1 = maxDigit 0 i then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s bkG.res.st.obl := by
    simp only [bkG.res]
    t3n [h28, CHAIN]
    try norm_num
  have st := symRun_sound bkG codeAt_kG s hpc hobl
  set u := bkG.res.toState s with hu
  have upc : u.pc = (if i < 51 then pcOf 710 else pcOf 709) := by
    simp only [hu, Result.toState_pc, bkG.res, E.eval, CmpOp.eval, h19]
    rw [ofNat_slt i 51 hi (by norm_num)]
    by_cases h : i < 51 <;> simp [h]
  have ur : RegsExcept s u [.x6, .x7, .x10, .x11, .x12] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, bkG.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    have hn' : ¬ (131552 ≤ A ∧ A < 131600) := by simpa [CHAIN] using hn
    simp only [hu, Result.toState_getMem, bkG.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)
  have u6 : u.getReg .x6 = BitVec.ofNat 64 3 := by simp [hu, bkG.res, rv_simp]
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
  -- 709 (i ≥ 51): t1 := 6
  obtain ⟨v, kv, sv, hkv, vpc, v6, vr, vm⟩ : ∃ v kv, Steps Images.keygenImage u kv kv v ∧
      kv = (if 51 ≤ i then 1 else 0) ∧ v.pc = pcOf 710 ∧
      v.getReg .x6 = BitVec.ofNat 64 (maxDigit 0 i - 1) ∧ RegsExcept u v [.x6] ∧ (∀ A, v.getMem A = u.getMem A) := by
    by_cases h51 : i < 51
    · rw [if_pos h51] at upc
      refine ⟨u, 0, Steps.refl _, by simp; omega, upc, ?_, fun _ _ => rfl, fun _ => rfl⟩
      rw [u6]; simp [maxDigit, h51]
    · rw [if_neg h51] at upc
      refine ⟨_, 1, symRun_sound bkG9 codeAt_kG9 u upc (by simp [bkG9.res, rv_simp]), by simp; omega,
        by simp [bkG9.res, E.eval], ?_, ?_, ?_⟩
      · simp [bkG9.res, rv_simp, maxDigit, h51]
      · intro r hr; simp at hr; cases r <;> simp_all [bkG9.res, rv_simp] <;> rfl
      · intro A; simp [bkG9.res, rv_simp]
  have hmd : maxDigit 0 i - 1 < 2 ^ 64 := by rw [kmd]; split <;> omega
  -- 710 `bne s4,t1,712`
  have stw := symRun_sound bkG10 codeAt_kG10 v vpc (by simp [bkG10.res, rv_simp])
  set w := bkG10.res.toState v with hw
  have v20 : v.getReg .x20 = BitVec.ofNat 64 m := by rw [vr.get (by simp), ur.get (by simp)]; exact h20
  have wpc : w.pc = (if m + 1 = maxDigit 0 i then pcOf 711 else pcOf 712) := by
    simp only [hw, Result.toState_pc, bkG10.res, E.eval, CmpOp.eval, v20, v6]
    rw [kne_of (by omega) hmd]
    have : (m ≠ maxDigit 0 i - 1) ↔ ¬ (m + 1 = maxDigit 0 i) := by rw [kmd]; split <;> omega
    by_cases h : m + 1 = maxDigit 0 i <;> simp_all
  have wr : ∀ r, w.getReg r = v.getReg r := by intro r; cases r <;> simp [hw, bkG10.res, rv_simp] <;> rfl
  have wm : ∀ A, w.getMem A = v.getMem A := by intro A; simp [hw, bkG10.res, rv_simp]
  have g : ∀ r, r ∉ [Reg.x6, .x7, .x10, .x11, .x12] → w.getReg r = s.getReg r := by
    intro r hr; rw [wr, vr.get (by simp at hr ⊢; tauto), ur.get hr]
  by_cases ht : m + 1 = maxDigit 0 i
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
theorem topIsG_iff {i : Nat} (hi : i < 54) : topIsG i = true ↔ i % 2 = 0 := by
  simp [topIsG]; omega

/-- Witness stack: one keygen chain rung (top tree, tree 0) from the end of the header (pc 135, `t3 = CHAIN`, header
words stored) to the loop head 118: the step block, its HASH, `jal 141` and `addi s4,s4,1; jal 118`. It computes
`T3.projHash (topChainHigh i m) (topChainInput leaf i m v)` and writes only `CHAIN+32 .. CHAIN+112`. -/
theorem kpair_rung (sk : BitVec 256) (t : MachineState) (hpc : t.pc = pcOf 135) (leaf i m : Nat) (v : Digest)
    (hi : i < 54) (hm : m < 8) (hmd : m < maxDigit 0 i)
    (h5 : t.getReg .x5 = 0) (h8 : t.getReg .x8 = BitVec.ofNat 64 0)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 i) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
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
      kg_spec u1 u1pc i m (by omega) (by omega) (by rw [g2 _ (by simp)]; exact h19)
        (by rw [g2 _ (by simp)]; exact h20) (by rw [g2 _ (by simp)]; exact h28)
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
      by_cases ht : m + 1 = maxDigit 0 i
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
        by_cases ht : m + 1 = maxDigit 0 i
        · rw [if_pos ht] at u212; exact hB _ u212 (Or.inr rfl)
        · rw [if_neg ht] at u212; exact hB _ u212 (Or.inl rfl)
      have hval : DigAt (writeHash u2 a) (CHAIN + 48) (T3.projHalf (topChainHigh i m) a) := by
        by_cases ht : m + 1 = maxDigit 0 i
        · have hh : topChainHigh i m = false := by simp [T3.topChainHigh, ht]
          rw [if_pos ht] at u212
          rw [hh]
          exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
        · have hlt : m + 1 < maxDigit 0 i := by omega
          have hh : topChainHigh i m = true := by simp [T3.topChainHigh, hG, hlt]
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
