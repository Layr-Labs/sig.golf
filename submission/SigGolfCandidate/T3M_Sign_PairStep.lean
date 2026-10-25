import SigGolfCandidate.T3M_Sign_SeedIndependent

/-! # The sign chain step block (G/F), witness stack (charge 86)

The sign chain routine at 1013 ends its header at 1030 (`sd t1,16(t3)` with `t3 = CHAIN`); 1031 jumps to the step
block at 1760 (the stage-1 block 1732..1757 is dead):

* G path (lower: `s0 ≠ 0`, `s3` odd; top: `s0 = 0`, `s3` even `≤ 52`): copy the header to `CHAIN+64/72`, zero
  `CHAIN+80 .. CHAIN+112`, hash the 64 bytes at `CHAIN+48` (`value | header | 0 | 0`) to `CHAIN+32` (interior steps:
  the HIGH half lands in the value slot) or to `CHAIN+48` (the terminal step: lower 6, top `maxDigit 0 i - 1`), then
  `s4 += 1; jal 1014`.
* F path: zero `CHAIN+32 .. CHAIN+48`, hash the 64 bytes at `CHAIN` to `CHAIN+48`, then the C3 tail trampoline at 1667
  (`jal 1667` at 1797).

`pair_rung` is the whole block from 1031 as a `TSim` of `WCT9.halfHash (chainHigh) (chainInputW)`. -/

namespace SigGolfCandidate.T3M.Sign.Seed
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open Keygen Keygen.PackedBlocks
open SigGolfCandidate.T3 (Layer Digest chainInput pad64 zero16 height chainHeader)
open SphincsSecurity (bytesLE bytesLE_length)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-! ### C3 (FULL): the chain tail trampoline at 1667 (moved here from `SeedChain`) -/
def ctr0 : List (BitVec 32) := [34181731]
def ctr1 : List (BitVec 32) := [33816675]
def ctr2 : List (BitVec 32) := [6292243,6954083]
def ctr3 : List (BitVec 32) := [134711,504247043,512635779,476985379,478034979,1706515,3662671983]
def ctr4 : List (BitVec 32) := [1706515,3662671983]
sym_block blkC0 := symRun { noAlias := true } ctr0 (pcOf 1667) 100
sym_block blkC1 := symRun { noAlias := true } ctr1 (pcOf 1668) 100
sym_block blkC2 := symRun { noAlias := true } ctr2 (pcOf 1669) 100
sym_block blkC3 := symRun { noAlias := true } ctr3 (pcOf 1671) 100
sym_block blkC4 := symRun { noAlias := true } ctr4 (pcOf 1676) 100
theorem blkC3_regs (t : MachineState) : RegsExcept t (blkC3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [blkC3.res, rv_simp] <;> rfl
/-- C3 (FULL): does the chain tail take the high half (chain 0 of a lower layer, after step 6)? -/
def hiSel (lay i m : Nat) : Prop := lay ≠ 0 ∧ i = 0 ∧ m = 6
instance (lay i m : Nat) : Decidable (hiSel lay i m) := by unfold hiSel; infer_instance
/-- C3 (FULL): extra steps of the F chain tail trampoline (from `jal 1667`) over 2. -/
def trX0 (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5

/-! ### Witness stack (charge 86): the step block 1760..1797 (top rule added; the old block 1732..1757 is dead)
* 1760 `beq s0,zero,1766`. Lower: 1761/1762 `andi t1,s3,1; beq t1,zero,1791` (F), 1763..1765 `t1 = 6; t2 = 0;
  jal 1776` (G). Top: 1766..1768 `t1 = s3 & 1; t2 = 0; bne t1,t2,1791` (odd: F), 1769/1770 `t2 = 52; blt t2,s3,1791`,
  1771..1774 `t1 = maxDigit 0 i - 1` (3, or 6 for `i ≥ 51`), 1775 `ld t2,24(t3)` (header high word).
* G body 1776..1788: copy the header `CHAIN+16` / `t2` to `CHAIN+64/72`, zero `CHAIN+80 .. CHAIN+112`, HASH the 64 bytes
  at `CHAIN+48` to `CHAIN+32` (interior: the HIGH half lands in the value slot) or to `CHAIN+48` (`s4 = t1`, the
  terminal step), then 1789/1790 `addi s4,s4,1; jal 1014`.
* F body 1791..1796 (unchanged) and 1797 `jal 1667` (the C3 trampoline). -/
def jmpS : List (BitVec 32) := [0x3650006f]
def sel0S : List (BitVec 32) := [0x00040c63]
def lselS : List (BitVec 32) := [0x0019f313, 0x06030a63]
def lgS : List (BitVec 32) := [0x00600313, 0x00000393, 0x02c0006f]
def tselS : List (BitVec 32) := [0x0019f313, 0x00000393, 0x04731e63]
/-- Campaign T51: 1769 `jal 1927` (the old 1769..1774 test/cap words are dead nops), and the GT block 1927..1936:
`t1 = 4 - [27 ≤ i < 48] + [i = 48]` (`maxDigit 0 i - 1` on the even chains `0 < i ≤ 50`), `bne s3,zero,1775`;
chain 0: `t1 = 7` (never the step index: chain 0 keeps the HIGH half on every step), `jal 1775`. -/
def tjS : List (BitVec 32) := [0x2780006f]
def gtAS : List (BitVec 32) := [0x00400313, 0xfe598393, 0x0153b393, 0x40730333, 0xfd098393, 0x0013b393, 0x00730333,
  0xd80992e3]
def gtBS : List (BitVec 32) := [0x00700313, 0xd7dff06f]
def thdrS : List (BitVec 32) := [0x018e3383]
def gS : List (BitVec 32) := [0x010e3f03, 0x05ee3023, 0x047e3423, 0x040e3823, 0x040e3c23, 0x060e3023, 0x060e3423,
  0x030e0513, 0x04000593, 0x020e0613, 0x006a1463]
def g6S : List (BitVec 32) := [0x030e0613]
def ecallS : List (BitVec 32) := [0x00000073]
def gtailS : List (BitVec 32) := [0x001a0a13, 0xbe0ff06f]
def fS : List (BitVec 32) := [0x020e3023,0x020e3423,0x000e0513,0x04000593,0x030e0613]
def ftailS : List (BitVec 32) := [0xdf9ff06f]
sym_block blkJ := symRun { noAlias := true } jmpS (pcOf 1031) 100
sym_block blkSel0 := symRun { noAlias := true } sel0S (pcOf 1760) 100
sym_block blkLsel := symRun { noAlias := true } lselS (pcOf 1761) 100
sym_block blkLg := symRun { noAlias := true } lgS (pcOf 1763) 100
sym_block blkTsel := symRun { noAlias := true } tselS (pcOf 1766) 100
sym_block blkTj := symRun { noAlias := true } tjS (pcOf 1769) 100
sym_block blkGtA := symRun { noAlias := true } gtAS (pcOf 1927) 100
sym_block blkGtB := symRun { noAlias := true } gtBS (pcOf 1935) 100
sym_block blkThdr := symRun { noAlias := true } thdrS (pcOf 1775) 100
sym_block blkG := symRun { noAlias := true } gS (pcOf 1776) 100
sym_block blkG6 := symRun { noAlias := true } g6S (pcOf 1787) 100
sym_block blkGt := symRun { noAlias := true } gtailS (pcOf 1789) 100
sym_block blkF := symRun { noAlias := true } fS (pcOf 1791) 100
sym_block blkFt := symRun { noAlias := true } ftailS (pcOf 1797) 100

/-- The step block, its two HASH sites and the C3 trampoline. -/
structure StepCode (im : Image) : Prop where
  jmp : CodeAt im (pcOf 1031) jmpS
  sel0 : CodeAt im (pcOf 1760) sel0S
  lsel : CodeAt im (pcOf 1761) lselS
  lg : CodeAt im (pcOf 1763) lgS
  tsel : CodeAt im (pcOf 1766) tselS
  tj : CodeAt im (pcOf 1769) tjS
  gtA : CodeAt im (pcOf 1927) gtAS
  gtB : CodeAt im (pcOf 1935) gtBS
  thdr : CodeAt im (pcOf 1775) thdrS
  g : CodeAt im (pcOf 1776) gS
  g6 : CodeAt im (pcOf 1787) g6S
  gcall : CodeAt im (pcOf 1788) ecallS
  gtail : CodeAt im (pcOf 1789) gtailS
  f : CodeAt im (pcOf 1791) fS
  fcall : CodeAt im (pcOf 1796) ecallS
  ftail : CodeAt im (pcOf 1797) ftailS
  tramp0 : CodeAt im (pcOf 1667) ctr0
  tramp1 : CodeAt im (pcOf 1668) ctr1
  tramp2 : CodeAt im (pcOf 1669) ctr2
  tramp3 : CodeAt im (pcOf 1671) ctr3
  tramp4 : CodeAt im (pcOf 1676) ctr4

/-- Witness stack: is the chain a top G chain (even, `≤ 50`, on the top tree; T51)? -/
def topG (lay i : Nat) : Prop := lay = 0 ∧ i % 2 = 0 ∧ i ≤ 50
instance (lay i : Nat) : Decidable (topG lay i) := by unfold topG; infer_instance

/-- Extra steps of one chain rung over `rungK` (old header + HASH + `addi; jal`). Lower G: the block (18 steps, 19 at
step 6) and `addi; jal`; top G: 22 steps (+1 for `i ≥ 51`, +1 at the terminal step `maxDigit 0 i - 1`) and
`addi; jal`; F: the block (9 below, 10 for an odd top chain, 12 for an even top chain `> 52`) and the C3 trampoline. -/
def trX (lay i m : Nat) : Nat :=
  if lay ≠ 0 ∧ i % 2 = 1 then (if m = 6 then 14 else 13)
  else if topG lay i then
    21 + (if i = 0 then 2 else 0) + (if i ≠ 0 ∧ m + 1 = SigGolfCandidate.T3.maxDigit 0 i then 1 else 0)
  else (if lay = 0 then (if i % 2 = 1 then 5 else 7) else 4) + trX0 lay i m

theorem ne_of' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem eq_of' {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem and1_ofNat (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

/-- C3 (FULL): the F chain tail `1797: jal 1667` and the trampoline 1667..1677. The HIGH half `hv` replaces the value
on chain 0 of a lower layer after step 6. -/
theorem tramp_spec {image : Image} (h : StepCode image) (s : MachineState)
    (hpc : s.pc = pcOf 1797) (lay i m : Nat) (hlay : lay < 2 ^ 64) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps image s (2 + trX0 lay i m) (2 + trX0 lay i m) t ∧ t.pc = pcOf (1013 + 1) ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧ DigAt t (CHAIN + 48) (if hiSel lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  -- 1797: jal 1667
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1667 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound blkFt h.ftail s hpc (by simp [blkFt.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [blkFt.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  -- the final `addi s4,s4,1; jal 1014` at 1676
  have last : ∀ u : MachineState, u.pc = pcOf 1676 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps image u 2 2 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound blkC4 h.tramp4 u hu (by simp [blkC4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [blkC4.res, E.eval]
    · simp only [Result.toState_getReg, blkC4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC4.res, rv_simp] <;> rfl
    · intro A _ _; simp [blkC4.res, rv_simp]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 1676 else pcOf 1668) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC0 h.tramp0 t0 p0 (by simp [blkC0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hi0 hh.2.1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trX0, hi0]) (by simp [trX0, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps image t1 1 1 t ∧ t.pc = (if lay = 0 then pcOf 1676 else pcOf 1669) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC1 h.tramp1 t1 p1 (by simp [blkC1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' hlay (by norm_num)]
      by_cases hl0 : lay = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hh.1 hl0
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trX0, hi0', hl0]) (by simp [trX0, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 1676 else pcOf 1671) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound blkC2 h.tramp2 t2 p2 (by simp [blkC2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, blkC2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of' (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [blkC2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [blkC2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ¬ hiSel lay i m := fun hh => hm6 hh.2.2
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trX0, hi0', hl0, hm6])
      (by simp [trX0, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [if_neg hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : hiSel lay i m := ⟨hl0, hi0', hm6'⟩
  have hobl : Oblig.all t3 blkC3.res.st.obl := by simp [blkC3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound blkC3 h.tramp3 t3 p3 hobl)).of_eq
    (by simp [trX0, hi0', hl0, hm6', blkC3.res]) (by simp [trX0, hi0', hl0, hm6', blkC3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkC3.res, E.eval]
  · simp only [Result.toState_getReg, blkC3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [if_pos hs]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, blkC3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (blkC3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (blkC3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, blkC3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)


/-- 1031 `jal 1760`, 1760 `beq s0,zero,1766`. -/
theorem jsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1031)
    (lay : Nat) (hlay : lay < 2 ^ 64) (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1766 else pcOf 1761) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  have st0 := symRun_sound blkJ hc.jmp s hpc (by simp [blkJ.res, rv_simp])
  set u0 := blkJ.res.toState s with hu0
  have u0pc : u0.pc = pcOf 1760 := by simp [hu0, blkJ.res, E.eval]
  have u0r : ∀ r, u0.getReg r = s.getReg r := by intro r; cases r <;> rfl
  have u0m : ∀ A, u0.getMem A = s.getMem A := by intro A; rfl
  have st1 := symRun_sound blkSel0 hc.sel0 u0 u0pc (by simp [blkSel0.res, rv_simp])
  refine ⟨_, (st0.trans st1).of_eq (by simp [blkJ.res, blkSel0.res]) (by simp [blkJ.res, blkSel0.res]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkSel0.res, E.eval, CmpOp.eval, u0r, h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' hlay (by norm_num)]
    by_cases hl0 : lay = 0 <;> simp [hl0]
  · intro r _; rw [← u0r r]; cases r <;> simp [blkSel0.res, rv_simp] <;> rfl
  · intro A _ _; rw [← u0m (BitVec.ofNat 64 A)]; simp [blkSel0.res, rv_simp]

/-- 1761 `andi t1,s3,1`, 1762 `beq t1,zero,1791`. -/
theorem lsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1761) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf 1791 else pcOf 1763) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkLsel hc.lsel s hpc (by simp [blkLsel.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkLsel.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, and1_ofNat]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, eq_of' (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [blkLsel.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkLsel.res, rv_simp]

/-- 1763..1765 `addi t1,zero,6; addi t2,zero,0; jal 1776` (lower G). -/
theorem lg_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1763) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1776 ∧ t.getReg .x6 = BitVec.ofNat 64 6 ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkLg hc.lg s hpc (by simp [blkLg.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkLg.res, E.eval]
  · simp [blkLg.res, rv_simp]
  · simp [blkLg.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [blkLg.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkLg.res, rv_simp]

/-- 1766..1768 `andi t1,s3,1; addi t2,zero,0; bne t1,t2,1791` (top). -/
theorem tsel_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1766) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i % 2 = 0 then pcOf 1769 else pcOf 1791) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkTsel hc.tsel s hpc (by simp [blkTsel.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, blkTsel.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, and1_ofNat]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [blkTsel.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkTsel.res, rv_simp]

/-- Campaign T51: the GT block's step index (`t1`). -/
def gtT (i : Nat) : Nat := if i = 0 then 7 else if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4
theorem gtT_top {i : Nat} (hi0 : i ≠ 0) (he : i % 2 = 0) : gtT i = SigGolfCandidate.T3.maxDigit 0 i - 1 := by
  unfold gtT SigGolfCandidate.T3.maxDigit
  simp only [if_pos rfl, if_neg hi0]
  split_ifs <;> omega
theorem maxDigit_top_bounds (i : Nat) : 4 ≤ SigGolfCandidate.T3.maxDigit 0 i ∧ SigGolfCandidate.T3.maxDigit 0 i ≤ 6 := by
  unfold SigGolfCandidate.T3.maxDigit
  simp only [if_pos rfl]
  split_ifs <;> omega
theorem gtA_x6 (i : Nat) (hi : i < 2 ^ 63) :
    ((4#64 - if (BitVec.ofNat 64 i - 27#64).ult 21#64 = true then 1#64 else 0#64) +
      if (BitVec.ofNat 64 i - 48#64).ult 1#64 = true then 1#64 else 0#64) =
    BitVec.ofNat 64 (if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4) := by
  have e1 : (BitVec.ofNat 64 i - 27#64).ult 21#64 = decide (27 ≤ i ∧ i < 48) := by
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_decide]
    omega
  have e2 : (BitVec.ofNat 64 i - 48#64).ult 1#64 = decide (i = 48) := by
    simp only [BitVec.ult, BitVec.toNat_sub, BitVec.toNat_ofNat, decide_eq_decide]
    omega
  rw [e1, e2]
  by_cases h1 : 27 ≤ i ∧ i < 48
  · have h2 : i ≠ 48 := by omega
    simp [h1, h2]
  · by_cases h2 : i = 48
    · subst h2; simp
    · simp [h1, h2]

/-- 1769 `jal 1927`, the GT block 1927..1936 (`t1 = gtT i`) and 1775 `ld t2,24(t3)` (header high word). -/
theorem gt_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1769) (i : Nat)
    (hi : i < 2 ^ 63) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (10 + (if i = 0 then 2 else 0)) (10 + (if i = 0 then 2 else 0)) t ∧ t.pc = pcOf 1776 ∧
      t.getReg .x6 = BitVec.ofNat 64 (gtT i) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  have s0 := symRun_sound blkTj hc.tj s hpc (by simp [blkTj.res, rv_simp])
  set u0 := blkTj.res.toState s with hu0
  have u0pc : u0.pc = pcOf 1927 := by simp [hu0, blkTj.res, E.eval]
  have u0r : ∀ r, u0.getReg r = s.getReg r := by intro r; cases r <;> rfl
  have u0m : ∀ A, u0.getMem A = s.getMem A := by intro A; rfl
  have st := symRun_sound blkGtA hc.gtA u0 u0pc (by simp [blkGtA.res, rv_simp])
  set u := blkGtA.res.toState u0 with hu
  have upc : u.pc = (if i ≠ 0 then pcOf 1775 else pcOf 1935) := by
    simp only [hu, Result.toState_pc, blkGtA.res, E.eval, CmpOp.eval, u0r, h19]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of' (by omega) (by norm_num)]
    by_cases h : i = 0 <;> simp [h]
  have u6 : u.getReg .x6 = BitVec.ofNat 64 (if 27 ≤ i ∧ i < 48 then 3 else if i = 48 then 5 else 4) := by
    simp only [hu, Result.toState_getReg, blkGtA.res, rv_simp, u0r, h19]
    exact gtA_x6 i hi
  have ur : RegsExcept u0 u [.x6, .x7] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, blkGtA.res, rv_simp] <;> rfl
  have um : ∀ A, u.getMem A = u0.getMem A := by intro A; simp [hu, blkGtA.res, rv_simp]
  obtain ⟨v, kv, sv, hkv, vpc, v6, vr, vm⟩ : ∃ v kv, Steps im u kv kv v ∧ kv = (if i = 0 then 2 else 0) ∧
      v.pc = pcOf 1775 ∧ v.getReg .x6 = BitVec.ofNat 64 (gtT i) ∧
      RegsExcept u v [.x6] ∧ (∀ A, v.getMem A = u.getMem A) := by
    by_cases h0 : i = 0
    · rw [if_neg (by simpa using h0)] at upc
      refine ⟨_, 2, symRun_sound blkGtB hc.gtB u upc (by simp [blkGtB.res, rv_simp]), by simp [h0],
        by simp [blkGtB.res, E.eval], ?_, ?_, ?_⟩
      · simp [blkGtB.res, rv_simp, gtT, h0]
      · intro r hr; simp at hr; cases r <;> simp_all [blkGtB.res, rv_simp] <;> rfl
      · intro A; simp [blkGtB.res, rv_simp]
    · rw [if_pos h0] at upc
      refine ⟨u, 0, Steps.refl _, by simp [h0], upc, ?_, fun _ _ => rfl, fun _ => rfl⟩
      rw [u6]; simp only [gtT, if_neg h0]
  have v28 : v.getReg .x28 = BitVec.ofNat 64 CHAIN := by
    rw [vr.get (by simp), ur.get (by simp), u0r]; exact h28
  have hobl : Oblig.all v blkThdr.res.st.obl := by
    simp only [blkThdr.res]
    t3n [v28, CHAIN]
    try norm_num
  have sw := symRun_sound blkThdr hc.thdr v vpc hobl
  have wr : RegsExcept v (blkThdr.res.toState v) [.x7] := by
    intro r hr; simp at hr; cases r <;> simp_all [blkThdr.res, rv_simp] <;> rfl
  have wm : ∀ A, (blkThdr.res.toState v).getMem A = v.getMem A := by intro A; simp [blkThdr.res, rv_simp]
  have w7 : (blkThdr.res.toState v).getReg .x7 = v.getMem (BitVec.ofNat 64 (CHAIN + 24)) := by
    simp only [Result.toState_getReg, blkThdr.res, rv_simp, v28]
    t3n [CHAIN]
  have u0r' : RegsExcept s u0 [] := fun r _ => u0r r
  refine ⟨_, (((s0.trans st).trans sv).trans sw).of_eq (by simp [hkv, blkTj.res, blkGtA.res, blkThdr.res]; omega)
    (by simp [hkv, blkTj.res, blkGtA.res, blkThdr.res]; omega), by simp [blkThdr.res, E.eval], ?_, ?_, ?_, ?_⟩
  · rw [wr.get (by simp)]; exact v6
  · rw [w7, vm, um, u0m]
  · exact (((u0r'.trans ur).trans vr).trans wr).mono (by simp)
  · intro A _ _; rw [wm, vm, um, u0m]

/-- The G body 1776..1786 (and 1787 at the terminal step `s4 = t1`): header copy, pads, HASH arguments. -/
theorem g_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1776) (m T : Nat)
    (hm : m < 2 ^ 63) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = BitVec.ofNat 64 T)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (11 + (if m = T then 1 else 0)) (11 + (if m = T then 1 else 0)) t ∧ t.pc = pcOf 1788 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = T then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getReg .x7 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12, .x30] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s blkG.res.st.obl := by
    simp only [blkG.res]
    t3n [h28, CHAIN]
    try norm_num
  have st := symRun_sound blkG hc.g s hpc hobl
  set u := blkG.res.toState s with hu
  have upc : u.pc = (if m = T then pcOf 1787 else pcOf 1788) := by
    simp only [hu, Result.toState_pc, blkG.res, E.eval, CmpOp.eval, h20, h6]
    rw [ne_of' (by omega) (by omega)]
    by_cases h : m = T <;> simp [h]
  have ur : RegsExcept s u [.x10, .x11, .x12, .x30] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, blkG.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    have hn' : ¬ (131552 ≤ A ∧ A < 131600) := by simpa [CHAIN] using hn
    simp only [hu, Result.toState_getMem, blkG.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp, h28]; rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp]
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, blkG.res, rv_simp, h28]; rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = s.getReg .x7 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, blkG.res]
      t3n [h28, CHAIN]
  by_cases ht : m = T
  · rw [if_pos ht] at upc
    have st6 := symRun_sound blkG6 hc.g6 u upc (by simp [blkG6.res, rv_simp])
    have wm : ∀ A, (blkG6.res.toState u).getMem A = u.getMem A := by intro A; simp [blkG6.res, rv_simp]
    have wr : RegsExcept u (blkG6.res.toState u) [.x12] := by
      intro r hr; simp at hr; cases r <;> simp_all [blkG6.res, rv_simp] <;> rfl
    refine ⟨_, (st.trans st6).of_eq (by simp [ht, blkG.res, blkG6.res]) (by simp [ht, blkG.res, blkG6.res]),
      by simp [blkG6.res, E.eval], by rw [wr.get (by simp)]; exact u10, by rw [wr.get (by simp)]; exact u11, ?_,
      by rw [wm]; exact umem.1, by rw [wm]; exact umem.2.1, by rw [wm]; exact umem.2.2.1,
      by rw [wm]; exact umem.2.2.2.1, by rw [wm]; exact umem.2.2.2.2.1, by rw [wm]; exact umem.2.2.2.2.2,
      (ur.trans wr).mono (by simp), fun A hA hn => (wm _).trans (uf A hA hn)⟩
    simp only [Result.toState_getReg, blkG6.res, rv_simp, if_pos ht, ur.get (show Reg.x28 ∉ _ by simp), h28]
    rfl
  · rw [if_neg ht] at upc
    refine ⟨u, st.of_eq (by simp [ht, blkG.res]) (by simp [ht, blkG.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg ht]; exact u12

/-- The F body 1791..1795: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1791)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 1796 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s blkF.res.st.obl := by
    simp only [blkF.res]
    t3n [h28, CHAIN]
    try norm_num
  refine ⟨_, symRun_sound blkF hc.f s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [blkF.res, E.eval]
  · simp only [Result.toState_getReg, blkF.res, rv_simp, h28]
  · simp only [Result.toState_getReg, blkF.res, rv_simp]
  · simp only [Result.toState_getReg, blkF.res, rv_simp, h28]; rfl
  · simp only [Result.toState_getMem, blkF.res]; t3n [h28, CHAIN]
  · simp only [Result.toState_getMem, blkF.res]; t3n [h28, CHAIN]
  · intro r hr; simp at hr; cases r <;> simp_all [blkF.res, rv_simp] <;> rfl
  · intro A hA hn
    have hn' : ¬ (A = 131520 ∨ A = 131528) := by simpa [CHAIN] using hn
    simp only [Result.toState_getMem, blkF.res]
    t3n [h28, CHAIN, Nat.mod_eq_of_lt hA]
    try (split_ifs <;> first | rfl | omega)

/-- 1789 `addi s4,s4,1`, 1790 `jal 1014`. -/
theorem gtail_spec {im : Image} (hc : StepCode im) (s : MachineState) (hpc : s.pc = pcOf 1789) (m : Nat)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf (1013 + 1) ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound blkGt hc.gtail s hpc (by simp [blkGt.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [blkGt.res, E.eval]
  · simp only [Result.toState_getReg, blkGt.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [blkGt.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGt.res, rv_simp]

/-! ### The whole rung after the header -/
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

/-- On an F chain the kept half is C3's `hiSel`. -/
theorem halfOf_chainHigh_F (lay : Layer) (i m : Nat) (hG : ClaudeWCT.WCT9.isG lay i = false) (a : BitVec 256) :
    ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a =
      if hiSel lay.val i m then a.extractLsb' 128 128 else a.extractLsb' 0 128 := by
  have hl : (lay ≠ 0) ↔ lay.val ≠ 0 := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (by rw [h']; rfl)⟩
  have h := ClaudeWCT.WCT9.chainHigh_eq_true_F (step := m) hG
  unfold hiSel
  cases hb : ClaudeWCT.WCT9.chainHigh lay i m
  · rw [if_neg]
    · rfl
    · intro hs
      have := h.mpr ⟨hl.mpr hs.1, hs.2.1, hs.2.2⟩
      rw [hb] at this; exact absurd this (by simp)
  · rw [if_pos]
    · rfl
    · obtain ⟨h1, h2, h3⟩ := h.mp hb; exact ⟨hl.mp h1, h2, h3⟩

/-- Witness stack: the G tail of a rung, from 1776 (`t1 = T`, `t2` = the header high word): the G body, its HASH
(`HIGH` half unless `m = T`) and `addi s4,s4,1; jal 1014`. -/
theorem g_rung {im : Image} (hc : StepCode im) (sk : BitVec 256) (t u : MachineState) (k : Nat)
    (su : Steps im t k k u) (upc : u.pc = pcOf 1776) (lay : Layer) (tree leaf i m T : Nat) (v : Digest)
    (hG : ClaudeWCT.WCT9.isG lay i = true) (hm : m < 2 ^ 63) (hT : T < 2 ^ 63)
    (hhi : m ≠ T → ClaudeWCT.WCT9.chainHigh lay i m = true)
    (hlo : m = T → ClaudeWCT.WCT9.chainHigh lay i m = false)
    (ur : RegsExcept t u [.x6, .x7]) (uf : Frame t u (fun _ => False))
    (h5 : t.getReg .x5 = 0) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 CHAIN) (u6 : u.getReg .x6 = BitVec.ofNat 64 T)
    (u7 : u.getReg .x7 = (chainHeader lay tree leaf i m).extractLsb' 64 64)
    (h16 : t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (chainHeader lay tree leaf i m).extractLsb' 0 64)
    (hv : DigAt t (CHAIN + 48) v) :
    TSim im sk t (k + 14 + (if m = T then 1 else 0)) (k + 21 + (if m = T then 1 else 0)) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' w => w.pc = pcOf (1013 + 1) ∧ w.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        DigAt w (CHAIN + 48) v' ∧ RegsExcept t w [.x6, .x7, .x10, .x11, .x12, .x20, .x30] ∧
        Frame t w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112)) := by
  rw [ClaudeWCT.WCT9.halfHash_eq]
  have g0 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t.getReg r := fun r hr => ur.get hr
  obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
    g_spec hc u upc m T hm hT u6 (by rw [g0 _ (by simp)]; exact h20) (by rw [g0 _ (by simp)]; exact h28)
  have f02 : Frame t u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
    (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
  have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
  have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
  have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v)) := by
    have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i m v
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
    rw [wordsOf_chainInputW_G hG, readWords_eight]
    rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
      show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
      show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
      show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
    rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), h16, u7]
  have hvalid : hashArgumentsValid u2 = true := by
    by_cases ht : m = T
    · rw [if_pos ht] at u212
      exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
        (by decide) (by decide)
    · rw [if_neg ht] at u212
      exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
        (by decide) (by decide)
  have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
  have hf2 : fetch im u2 = some (.base .ECALL) := (hc.gcall.fetch u2 u2pc).trans rfl
  refine (TSim.steps (su.trans su2) (TSim.publicHash_bind (k := 2) (c := 2) (n := 0) (b := 0)
    hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 m := by
      rw [getReg_writeHash, r02.get (by simp)]; exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec hc (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) m hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases ht : m = T
      · rw [if_pos ht] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg ht] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a) := by
      by_cases ht : m = T
      · rw [if_pos ht] at u212
        rw [hlo ht]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg ht] at u212
        rw [hhi ht]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    refine TSim.pure_steps sw ⟨wpc, w20, hval.frame wf (by decide) (by simp) (by simp), ?_, ?_⟩
    · have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      exact ((r02.trans rr).trans wr).mono (by simp)
    · exact ((f02.trans hwf).trans wf).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim)
  all_goals (try simp only [chainInputW_blocks])
  all_goals (by_cases ht : m = T <;> (try simp [ht]) <;> omega)

/-- Witness stack: one chain rung from the end of the header (pc 1031, `t3 = CHAIN`, header words stored) to the
loop head 1014: the step block 1760.., its HASH, and the tail (G: `addi; jal`; F: the C3 trampoline). It computes
`WCT9.halfHash (chainHigh) (chainInputW)` (top G chains: the top rule, terminal step `maxDigit 0 i - 1`) and writes
only `CHAIN+32 .. CHAIN+112`. -/
theorem pair_rung {im : Image} (hc : StepCode im) (sk : BitVec 256) (t : MachineState)
    (hpc : t.pc = pcOf 1031) (lay : Layer) (tree leaf i m : Nat) (v : Digest)
    (hi : i < 51) (hm : m < 8) (hm7 : lay.val ≠ 0 → m < 7)
    (hmt : lay.val = 0 → m < SigGolfCandidate.T3.maxDigit 0 i)
    (h5 : t.getReg .x5 = 0) (h8 : t.getReg .x8 = BitVec.ofNat 64 lay.val)
    (h19 : t.getReg .x19 = BitVec.ofNat 64 i) (h20 : t.getReg .x20 = BitVec.ofNat 64 m)
    (h28 : t.getReg .x28 = BitVec.ofNat 64 CHAIN)
    (hz0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0) (hz8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0)
    (h16 : t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (chainHeader lay tree leaf i m).extractLsb' 0 64)
    (h24 : t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (chainHeader lay tree leaf i m).extractLsb' 64 64)
    (hhz : (chainHeader lay tree leaf i m).extractLsb' 64 64 = 0)
    (hv : DigAt t (CHAIN + 48) v) :
    TSim im sk t (8 + trX lay.val i m) (15 + trX lay.val i m) 1 1
      (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i m)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i m v))
      (fun v' w => w.pc = pcOf (1013 + 1) ∧ w.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        DigAt w (CHAIN + 48) v' ∧ RegsExcept t w [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30] ∧
        Frame t w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∧
        (¬ (lay.val ≠ 0 ∧ i % 2 = 1) → ¬ topG lay.val i → w.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧
          w.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
          Frame t w (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40 ∨ (CHAIN + 48 ≤ A ∧ A < CHAIN + 80)))) := by
  have hlay : lay.val < 4 := lay.isLt
  have hl : (lay ≠ 0) ↔ lay.val ≠ 0 := ⟨fun h h' => h (Fin.ext h'), fun h h' => h (by rw [h']; rfl)⟩
  obtain ⟨u, su, upc, ur, uf⟩ := jsel_spec hc t hpc lay.val (by omega) h8
  have g0 : ∀ r, r ∉ ([] : List Reg) → u.getReg r = t.getReg r := fun r hr => ur.get hr
  by_cases hLG : lay.val ≠ 0 ∧ i % 2 = 1
  · -- lower G
    rw [if_neg hLG.1] at upc
    obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := lsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
    rw [if_neg (by omega)] at u1pc
    obtain ⟨u2, su2, u2pc, u26, u27, u2r, u2f⟩ := lg_spec hc u1 u1pc
    have hGb : ClaudeWCT.WCT9.isG lay i = true := ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨hl.mpr hLG.1, hLG.2⟩)
    have hm6 := hm7 hLG.1
    have run := g_rung hc sk t u2 _ (su.trans (su1.trans su2)) u2pc lay tree leaf i m 6 v hGb (by omega) (by norm_num)
      (fun h => ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inl ⟨hl.mpr hLG.1, Or.inr ⟨hLG.2, by omega⟩⟩))
      (fun h => by subst h; exact ClaudeWCT.WCT9.chainHigh_six (by omega))
      ((ur.trans (u1r.trans u2r)).mono (by simp)) ((uf.trans (u1f.trans u2f)).mono (fun A _ h => by simp_all))
      h5 h20 h28 u26 (by rw [u27, hhz]; rfl) h16 hv
    refine (run.of_eq rfl ?_ ?_ rfl rfl).mono ?_
    · simp only [trX, if_pos hLG]; split_ifs <;> omega
    · simp only [trX, if_pos hLG]; split_ifs <;> omega
    · intro v' w hw
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1.mono (by simp), hw.2.2.2.2, fun hF => absurd hLG hF⟩
  by_cases hTG : topG lay.val i
  · -- top G
    obtain ⟨hl0, he, h50⟩ := hTG
    have hl0' : lay = 0 := Fin.ext hl0
    rw [if_pos hl0] at upc
    obtain ⟨u1, su1, u1pc, u1r, u1f⟩ := tsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
    rw [if_pos he] at u1pc
    obtain ⟨u3, su3, u3pc, u36, u37, u3r, u3f⟩ := gt_spec hc u1 u1pc i (by omega)
      (by rw [u1r.get (by simp), g0 _ (by simp)]; exact h19)
      (by rw [u1r.get (by simp), g0 _ (by simp)]; exact h28)
    have f01 : Frame t u1 (fun _ => False) := (uf.trans u1f).mono (fun A _ h => by simp_all)
    have hGb : ClaudeWCT.WCT9.isG lay i = true := ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl0', he, h50⟩)
    have hmd := hmt hl0
    have hmb := maxDigit_top_bounds i
    have key : m = gtT i ↔ (i ≠ 0 ∧ m + 1 = SigGolfCandidate.T3.maxDigit 0 i) := by
      by_cases hi0 : i = 0
      · subst hi0; simp only [gtT, if_true]; constructor
        · intro h; omega
        · intro h; exact absurd rfl h.1
      · rw [gtT_top hi0 he]; constructor
        · intro h; exact ⟨hi0, by omega⟩
        · intro h; omega
    have run := g_rung hc sk t u3 _ (su.trans (su1.trans su3)) u3pc lay tree leaf i m
      (gtT i) v hGb (by omega) (by unfold gtT; split_ifs <;> omega)
      (fun h => ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inr ⟨hl0', ⟨he, h50⟩, by
        by_cases hi0 : i = 0
        · exact Or.inr hi0
        · left; have := gtT_top hi0 he; omega⟩))
      (fun h => by
        cases hb : ClaudeWCT.WCT9.chainHigh lay i m
        · rfl
        · rcases ClaudeWCT.WCT9.chainHigh_eq_true.mp hb with ⟨h1, -⟩ | ⟨-, -, h3⟩
          · exact absurd hl0' h1
          · have := key.mp h; omega)
      ((ur.trans (u1r.trans u3r)).mono (by simp))
      ((f01.trans u3f).mono (fun A _ h => by simp_all))
      h5 h20 h28 u36 (by rw [u37, f01.get (by decide) (by simp)]; exact h24) h16 hv
    refine (run.of_eq rfl ?_ ?_ rfl rfl).mono ?_
    · have hnLG : ¬ (lay.val ≠ 0 ∧ i % 2 = 1) := fun h => h.1 hl0
      have hT : topG lay.val i := ⟨hl0, he, h50⟩
      simp only [trX, if_neg hnLG, if_pos hT]
      by_cases hi0 : i = 0 <;> by_cases ht : m = gtT i <;>
        simp only [hi0, ht, if_true, if_false] <;> split_ifs <;> simp_all <;> omega
    · have hnLG : ¬ (lay.val ≠ 0 ∧ i % 2 = 1) := fun h => h.1 hl0
      have hT : topG lay.val i := ⟨hl0, he, h50⟩
      simp only [trX, if_neg hnLG, if_pos hT]
      by_cases hi0 : i = 0 <;> by_cases ht : m = gtT i <;>
        simp only [hi0, ht, if_true, if_false] <;> split_ifs <;> simp_all <;> omega
    · intro v' w hw
      exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1.mono (by simp), hw.2.2.2.2,
        fun _ hF => absurd ⟨hl0, he, h50⟩ hF⟩
  -- F path
  have hGb : ClaudeWCT.WCT9.isG lay i = false := by
    cases hb : ClaudeWCT.WCT9.isG lay i
    · rfl
    · rcases ClaudeWCT.WCT9.isG_eq_true.mp hb with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
      · exact absurd ⟨hl.mp h1, h2⟩ hLG
      · exact absurd ⟨by rw [h1]; rfl, h2, h3⟩ hTG
  rw [ClaudeWCT.WCT9.halfHash_eq, ClaudeWCT.WCT9.chainInputW_F hGb]
  -- reach 1791
  obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t (2 + k1) (2 + k1) u1 ∧
      k1 = (if lay.val = 0 then (if i % 2 = 1 then 3 else 5) else 2) ∧ u1.pc = pcOf 1791 ∧
      RegsExcept t u1 [.x6, .x7] ∧ Frame t u1 (fun _ => False) := by
    by_cases hl0 : lay.val = 0
    · rw [if_pos hl0] at upc
      obtain ⟨u2, su2, u2pc, u2r, u2f⟩ := tsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
      by_cases ho : i % 2 = 1
      · rw [if_neg (by omega)] at u2pc
        exact ⟨u2, 3, su.trans su2, by rw [if_pos hl0, if_pos ho], u2pc, (ur.trans u2r).mono (by simp),
          (uf.trans u2f).mono (fun A _ h => by simp_all)⟩
      · exact absurd ⟨hl0, by omega, by omega⟩ hTG
    · rw [if_neg hl0] at upc
      obtain ⟨u2, su2, u2pc, u2r, u2f⟩ := lsel_spec hc u upc i (by rw [g0 _ (by simp)]; exact h19)
      rw [if_pos (by omega)] at u2pc
      exact ⟨u2, 2, su.trans su2, by rw [if_neg hl0], u2pc, (ur.trans u2r).mono (by simp),
        (uf.trans u2f).mono (fun A _ h => by simp_all)⟩
  have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u1.getReg r = t.getReg r := fun r hr => u1r.get hr
  obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
    f_spec hc u1 u1pc (by rw [g1 _ (by simp)]; exact h28)
  have f02 : Frame t u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
    (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h; exact False.elim h; exact h)
  have r02 : RegsExcept t u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
  have v2 := hv.frame f02 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
  have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i m v)) := by
    have hl := Keygen.chainInput_length lay tree leaf i m v
    rw [pad64_of_aligned _ (by rw [hl])]
    refine hashInput_toQ u2 _ 0 CHAIN hl u210 (by decide) (by decide) u211 (by decide) ?_
    rw [Keygen.wordsOf_chainInput, readWords_eight,
      f02 CHAIN (by decide) (by simp only [CHAIN]; omega), f02 (CHAIN + 8) (by decide) (by simp only [CHAIN]; omega),
      f02 (CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
      f02 (CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), hz0, hz8, h16, h24, u232, u240, v2.1, v2.2]
  have hvalid : hashArgumentsValid u2 = true :=
    hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
      (by decide) (by decide)
  have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp)]; exact h5
  have hf2 : fetch im u2 = some (.base .ECALL) := (hc.fcall.fetch u2 u2pc).trans rfl
  refine (TSim.steps (su1.trans su2) (TSim.publicHash_bind (k := 2 + trX0 lay.val i m)
    (c := 2 + trX0 lay.val i m) (n := 0) (b := 0)
    (f := fun a => pure (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i m) a))
    hf2 h5' hvalid hq (fun a => ?_))).of_eq rfl ?_ ?_ ?_ ?_
  · obtain ⟨w, sw, wpc, w20, wv, wr, wf⟩ := tramp_spec hc (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) lay.val i m (by omega) (by omega) (by omega)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h8)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h19)
      (by rw [getReg_writeHash, r02.get (by simp)]; exact h20) _ _
      (DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide))
      (DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by decide))
    have hwf := Frame.writeHash u2 a (CHAIN + 48) u212 (by decide)
    have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
    have fw : Frame u2 w (fun A => (CHAIN + 48 ≤ A ∧ A < CHAIN + 80) ∨ (A = CHAIN + 48 ∨ A = CHAIN + 56)) :=
      hwf.trans wf
    refine TSim.pure_steps sw ⟨wpc, w20, ?_, ((r02.trans rr).trans wr).mono (by simp), ?_, fun _ _ => ⟨?_, ?_, ?_⟩⟩
    · rw [halfOf_chainHigh_F lay i m hGb]; exact wv
    · exact (f02.trans fw).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; omega)
    · rw [fw.get (by decide) (by simp only [CHAIN]; omega)]; exact u232
    · rw [fw.get (by decide) (by simp only [CHAIN]; omega)]; exact u240
    · exact (f02.trans fw).mono (fun A _ h => by
        simp only [CHAIN] at h ⊢; omega)
  all_goals simp only [trX, if_neg hLG, if_neg hTG, hk1, Keygen.toQ_chainInput_blocks]
  all_goals by_cases hl0 : lay.val = 0 <;> by_cases ho : i % 2 = 1 <;> simp [hl0, ho] <;> omega

/-! ### Sign chain loop state (pairing stage 1)
`ChainPreS` is `Keygen.ChainPre` without the pad zeros `CHAIN+32/40` (the F path now clears them itself and a G step
overwrites them), with the value slot kept clear of the widened scratch `CHAIN+32 .. CHAIN+112` and lower chains of at
most 7 steps. `ChainWS` is the widened chain write set. -/
structure ChainPreS (s : MachineState) (lay : Layer) (tree leaf i cap e valp ret : Nat) : Prop where
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
  he : e ≤ 8
  hlow : lay.val ≠ 0 → e ≤ 7
  hv8 : valp % 8 = 0
  hv : valp + 16 ≤ 2 ^ 24
  hvc : valp + 16 ≤ CHAIN ∨ CHAIN + 112 ≤ valp
  z0 : s.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : s.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def ChainWS (valp A : Nat) : Prop :=
  (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112) ∨ (valp ≤ A ∧ A < valp + 16)
structure ChainHeadS (b : Nat) (s0 : MachineState) (valp m : Nat) (v : Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 1)
  x20 : t.getReg .x20 = BitVec.ofNat 64 m
  regs : RegsExcept s0 t chainRegs
  frame : Frame s0 t (ChainWS valp)
  val : DigAt t (CHAIN + 48) v
theorem ChainWS_of_chainW {valp A : Nat} (h : ChainW valp A) : ChainWS valp A := by
  unfold ChainW at h; unfold ChainWS; simp only [CHAIN] at *; omega

/-- The F pad words `CHAIN+32/40` are zero. -/
def Z32 (t : MachineState) : Prop :=
  t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0
/-- An F chain (not a pairing-stage-1 G chain). -/
def FCh (lay : Layer) (i : Nat) : Prop := ¬ (lay.val ≠ 0 ∧ i % 2 = 1)
theorem Z32.frame {s t : MachineState} {W : Nat → Prop} (h : Z32 s) (hf : Frame s t W)
    (h32 : ¬ W (CHAIN + 32)) (h40 : ¬ W (CHAIN + 40)) : Z32 t :=
  ⟨(hf.get (by decide) h32).trans h.1, (hf.get (by decide) h40).trans h.2⟩
theorem FCh_top (i : Nat) : FCh 0 i := fun h => h.1 rfl

end SigGolfCandidate.T3M.Sign.Seed
