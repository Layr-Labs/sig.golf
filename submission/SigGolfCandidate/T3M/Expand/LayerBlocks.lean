import SigGolfCandidate.T3M.Expand.Blocks
import SigGolfCandidate.T3M.Sign.Basic
import SigGolfCandidate.T3M.Expand.PackedHeader
import SigGolfCandidate.T3M.Keygen.Tree

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev ENC : Nat := 0x20260
abbrev NODE : Nat := 0x20200
def hookCode : List (BitVec 32) := [0x5392606f]
sym_block hookCodeBlock := symRun { noAlias := true } hookCode (pcOf 1117) 30
def testCode : List (BitVec 32) := [0x41478e33,0xfffe0e13]
def branch1Code : List (BitVec 32) := [34479715]
def branch2Code : List (BitVec 32) := [33819747]
def pairCode : List (BitVec 32) := [134967,638521107,134839,537824915,963331,9352067,7286819,8336419,51294979,59683715,40843299,41892899,32871]
sym_block pairCodeBlock := symRun { noAlias := true } pairCode (pcOf 40879) 30
def backCode : List (BitVec 32) := [0xa8cd906f]
sym_block backCodeBlock := symRun { noAlias := true } backCode (pcOf 40892) 30
def selectCode : List (BitVec 32) := testCode ++ branch1Code
sym_block selectBlock := symRun { noAlias := true } selectCode (pcOf 40875) 30
sym_block layerBranch := symRun { noAlias := true } branch2Code (pcOf 40878) 30
def remaining (s : MachineState) : Word := s.getReg .x15 - s.getReg .x20 - 1
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
abbrev CHAIN : Nat := 0x201A0
abbrev LEAFPK : Nat := 0x20600
macro "ex_regs" res:ident : tactic =>
  `(tactic| (intro r hr
             simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
             cases r <;> simp_all [rv_simp, $res:ident] <;> rfl))
theorem ex_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := ofNat_slt a b ha hb
theorem ex_beq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · have : BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun he => h ((ofNat_inj ha hb).mp he)
    simp [this, h]
def e_hdrA : List (BitVec 32) := [1050259,29791923,1707539,29974067,29787827,710049903]
sym_block eb_hdrA := symRun { noAlias := true } e_hdrA (pcOf 1119) 30
/-- C4: the top fold label is the heap (`t1 = a3`) with a zero high word (`t2 = 0`). -/
def e_hdrB : List (BitVec 32) := [915,426771,33817187]
sym_block eb_hdrB := symRun { noAlias := true } e_hdrB (pcOf 42765) 30
def e_hdrC : List (BitVec 32) := [17077011,538141459,0xfff40f13,51322643,31679283,0xc100f13,59711251,756023407]
sym_block eb_hdrC := symRun { noAlias := true } e_hdrC (pcOf 42768) 30
def e_hdrD : List (BitVec 32) := [0xd44d706f]
sym_block eb_hdrD := symRun { noAlias := true } e_hdrD (pcOf 42776) 30
def e_hdrE : List (BitVec 32) := [134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
sym_block eb_hdrE := symRun { noAlias := true } e_hdrE (pcOf 1129) 30
def e_hpA : List (BitVec 32) := [0xf49333,19071795,16978707,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,267875]
sym_block eb_hpA := symRun { noAlias := true } e_hpA (pcOf 42741) 30
/-- R6 expand (EXP image swap): `42755 j KPAD` (49819). -/
def e_hpZ : List (BitVec 32) := [0x6610606f]
/-- KPAD (49819..49825): zero the leaf's pad16 (`LEAFPK + 0..15`) and the 32-byte pad (`LEAFPK + 32..63`), then
`j 1009`. -/
def e_kpad : List (BitVec 32) := [0xe3023,0xe3423,0x20e3023,0x20e3423,0x20e3823,0x20e3c23,0xd40d006f]
sym_block eb_kpad := symRun { noAlias := true } e_kpad (pcOf 49819) 30
/-- KMAX (49812..49818): `x21` = top chain cap 7 (i >= s11 = 51), 4 (i >= 24), 5; then `j 1031`. -/
def e_kmax0 : List (BitVec 32) := [0x700a93,0x1b9da63]
sym_block eb_kmax0 := symRun { noAlias := true } e_kmax0 (pcOf 49812) 30
def e_kmax1 : List (BitVec 32) := [0x400a93,0x1800e13,0x1c9d463]
sym_block eb_kmax1 := symRun { noAlias := true } e_kmax1 (pcOf 49814) 30
def e_kmax2 : List (BitVec 32) := [0x500a93,0xdb4d006f]
sym_block eb_kmax2 := symRun { noAlias := true } e_kmax2 (pcOf 49817) 30
def e_kmax3 : List (BitVec 32) := [0xdb4d006f]
sym_block eb_kmax3 := symRun { noAlias := true } e_kmax3 (pcOf 49818) 30
sym_block eb_hpZ := symRun { noAlias := true } e_hpZ (pcOf 42755) 30
def e_hpJ : List (BitVec 32) := [0xbb0d706f]
sym_block eb_hpJ := symRun { noAlias := true } e_hpJ (pcOf 42757) 30
def e_w1009 : List (BitVec 32) := [2451]
sym_block eb_w1009 := symRun { noAlias := true } e_w1009 (pcOf 1009) 30
def e_slA : List (BitVec 32) := [4824595,264291]
sym_block eb_slA := symRun { noAlias := true } e_slA (pcOf 42758) 30
def e_slB : List (BitVec 32) := [624739]
sym_block eb_slB := symRun { noAlias := true } e_slB (pcOf 42760) 30
def e_slN : List (BitVec 32) := [17698323,0xc48d706f]
sym_block eb_slN := symRun { noAlias := true } e_slN (pcOf 42761) 30
/-- R6 expand (EXP image swap): `42763 addi t3,t3,64` (top slot of chain i at leaf + 64 + 16 i). -/
def e_slT : List (BitVec 32) := [0x40e0e13,0xc40d706f]
sym_block eb_slT := symRun { noAlias := true } e_slT (pcOf 42763) 30
def e_slZ : List (BitVec 32) := [0xc40d706f]
sym_block eb_slZ := symRun { noAlias := true } e_slZ (pcOf 42764) 30
/-! C2 + C3 (FULL) trampolines: chain tail at 43451 (from 1047), left-child current value at 43462 (from 1103),
packed lower node word at 43467 (from 42775). -/
def e_hdrT : List (BitVec 32) := [31679283,13828915,1475543827,915,2795331695]
sym_block eb_hdrT := symRun { noAlias := true } e_hdrT (pcOf 43467) 30
def e_ct0 : List (BitVec 32) := [34181731]
sym_block eb_ct0 := symRun { noAlias := true } e_ct0 (pcOf 43451) 30
def e_ct1 : List (BitVec 32) := [33816675]
sym_block eb_ct1 := symRun { noAlias := true } e_ct1 (pcOf 43452) 30
def e_ct2 : List (BitVec 32) := [6292243,6954083]
sym_block eb_ct2 := symRun { noAlias := true } e_ct2 (pcOf 43453) 30
def e_ct3 : List (BitVec 32) := [134711,504247043,512635779,476985379,478034979,1706515,2426232943]
sym_block eb_ct3 := symRun { noAlias := true } e_ct3 (pcOf 43455) 30
def e_ct4 : List (BitVec 32) := [1706515,2426232943]
sym_block eb_ct4 := symRun { noAlias := true } e_ct4 (pcOf 43460) 30
/-- C4: the top layer's left child also reads the high half (the `beq s0` skip is a NOP). -/
def e_lcA : List (BitVec 32) := [134839,604933779,19]
sym_block eb_lcA := symRun { noAlias := true } e_lcA (pcOf 43462) 30
def e_lcB : List (BitVec 32) := [17731219,2715639919]
sym_block eb_lcB := symRun { noAlias := true } e_lcB (pcOf 43465) 30
def e_lcC : List (BitVec 32) := [2715639919]
def e_lcD : List (BitVec 32) := [134967,537857811,963331,9352067,7286819,8336419,134967,588189459,733955,9122691,7286819,8336419]
sym_block eb_lcD := symRun { noAlias := true } e_lcD (pcOf 1105) 30
/-- C3 (FULL): extra steps of the chain tail trampoline over the old `addi s4; jal` (2 steps). -/
def trXE (lay i m : Nat) : Nat := if i ≠ 0 then 2 else if lay = 0 then 3 else if m = 6 then 10 else 5
theorem trXE_le (lay i m : Nat) : trXE lay i m ≤ 10 := by unfold trXE; split_ifs <;> omega
/-- C2 (FULL) + C4: offset of the current value (a left child) in the node output: every layer reads the high half. -/
def hiOff (_lay : Nat) : Nat := 16
def slotOff (lay : T3.Layer) (c : Nat) : Nat := if lay = 0 then 16 * c + 64 else if c = 0 then 0 else 16 * c + 16
def hpK (lay : T3.Layer) : Nat := if lay = 0 then 24 else 17
/-- R6 top leaf: the 32-byte pad words `LEAFPK + 32 .. LEAFPK + 56` (zeroed by KPAD). -/
def TopPadW (A : Nat) : Prop := A = LEAFPK + 32 ∨ A = LEAFPK + 40 ∨ A = LEAFPK + 48 ∨ A = LEAFPK + 56
def TopPadZero (t : MachineState) : Prop :=
  t.getMem (BitVec.ofNat 64 (LEAFPK + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 40)) = 0 ∧
    t.getMem (BitVec.ofNat 64 (LEAFPK + 48)) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 56)) = 0
def slK (lay : T3.Layer) (i : Nat) : Nat := if lay = 0 then 5 else if i = 0 then 5 else 6
def hdrK (lay : Nat) : Nat := if lay = 0 then 19 else 31
section blocks
variable (s : MachineState)
theorem lbu_word1027 : decodeInstruction (0x000e4a03 : BitVec 32) = some (.base (.LBU .x20 .x28 0)) := rfl
theorem eb_ct3_regs (t : MachineState) : RegsExcept t (eb_ct3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [eb_ct3.res, rv_simp] <;> rfl
theorem ex_ne (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
  fun he => h ((ofNat_inj hx hy).mp he)
theorem ex_valid (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem eb_hdrT_regs (t : MachineState) : RegsExcept t (eb_hdrT.res.toState t) [.x6, .x7] := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  cases r <;> simp_all [eb_hdrT.res, rv_simp] <;> rfl
theorem eb_hdrT_frame (t : MachineState) : Frame t (eb_hdrT.res.toState t) (fun _ => False) := by
  intro A _ _; simp [eb_hdrT.res, rv_simp]
theorem eb_hdrT_x6 (t : MachineState) :
    (eb_hdrT.res.toState t).getReg .x6 = (t.getReg .x6 ||| t.getReg .x30) + t.getReg .x13 + BitVec.ofNat 64 1407 := by
  simp only [Result.toState_getReg, eb_hdrT.res, rv_simp]
theorem eb_hdrT_x7 (t : MachineState) : (eb_hdrT.res.toState t).getReg .x7 = 0 := by
  simp only [Result.toState_getReg, eb_hdrT.res, rv_simp]
theorem eb_hdrE_regs (t : MachineState) : RegsExcept t (eb_hdrE.res.toState t) [.x10, .x11, .x12, .x28] := by
  intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  cases r <;> simp_all [eb_hdrE.res, rv_simp] <;> rfl
theorem eb_hdrT_pc (t : MachineState) : (eb_hdrT.res.toState t).pc = pcOf 1129 := by
  simp [Result.toState_pc, eb_hdrT.res, E.eval]
/-- the node tweak words written at `NODE + 16` / `NODE + 24`: `WCT9.merkleTweak` (C2 packed word for lower layers). -/
theorem merkleTweak_words_top (tree heap : Nat) (h1 : 1 ≤ heap) (hh : heap < 4096) :
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 0 64 = BitVec.ofNat 64 heap ∧
    (ClaudeWCT.WCT9.merkleTweak 0 tree heap).extractLsb' 64 64 = 0 := by
  rw [ClaudeWCT.WCT9.merkleTweak_top_low, ClaudeWCT.WCT9.merkleTweak_top_high, T3.topNodeWord_eq h1 hh]
  exact ⟨rfl, rfl⟩
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
class Code (im : Image) : Prop where
  hookCode_at : CodeAt im (pcOf 1117) hookCode
  testCode_at : CodeAt im (pcOf 40875) testCode
  branch1Code_at : CodeAt im (pcOf 40877) branch1Code
  branch2Code_at : CodeAt im (pcOf 40878) branch2Code
  pairCode_at : CodeAt im (pcOf 40879) pairCode
  backCode_at : CodeAt im (pcOf 40892) backCode
  selectCode_at : CodeAt im (pcOf 40875) selectCode
variable {im : Image} [Code im]
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 40879) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairCodeBlock.res.st.obl := by
    simp [pairCodeBlock.res, rv_simp]
  refine ⟨_, symRun_sound pairCodeBlock (Code.pairCode_at (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pairCodeBlock.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · simp only [Result.toState_getMem, pairCodeBlock.res, ENC, NODE]
    t3n []
  · intro r hr; simp at hr; cases r <;> simp_all [pairCodeBlock.res, rv_simp]; rfl
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, pairCodeBlock.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem select_spec (s : MachineState) (hpc : s.pc = pcOf 40875) :
    ∃ t, Steps im s 3 3 t ∧
      t.pc = (if remaining s = 0 then pcOf 40878 else pcOf 40892) ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound selectBlock (Code.selectCode_at (im := im)) s hpc (by simp [selectBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · simp [Result.toState_getReg, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · intro r hr; simp at hr; cases r <;> simp_all [selectBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, selectBlock.res, rv_simp]

theorem layer_spec (s : MachineState) (hpc : s.pc = pcOf 40878) :
    ∃ t, Steps im s 1 1 t ∧
      t.pc = (if s.getReg .x8 = 0 then pcOf 40892 else pcOf 40879) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound layerBranch (Code.branch2Code_at (im := im)) s hpc (by simp [layerBranch.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, layerBranch.res, rv_simp]
  · intro r hr; cases r <;> simp [layerBranch.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, layerBranch.res, rv_simp]

theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1117) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 40875 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hookCodeBlock (Code.hookCode_at (im := im)) s hpc (by simp [hookCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, hookCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [hookCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, hookCodeBlock.res, rv_simp]

theorem back_spec (s : MachineState) (hpc : s.pc = pcOf 40892) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1119 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound backCodeBlock (Code.backCode_at (im := im)) s hpc (by simp [backCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, backCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [backCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, backCodeBlock.res, rv_simp]

theorem continue_spec (s : MachineState) (hpc : s.pc = pcOf 1117)
    (hc : remaining s ≠ 0 ∨ s.getReg .x8 = 0) :
    ∃ t k, Steps im s k k t ∧ k ≤ 6 ∧ t.pc = pcOf 1119 ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = remaining s := by
    unfold remaining
    rw [ur.get (by simp), ur.get (by simp)]
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [he] at vp v28
  by_cases hz : remaining s = 0
  · rw [if_pos hz] at vp
    have h8 : v.getReg .x8 = 0 := by
      rw [vr.get (by simp), ur.get (by simp)]
      exact hc.resolve_left (not_not_intro hz)
    obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
    rw [if_pos h8] at wp
    obtain ⟨t, wt, tp, tr, tf⟩ := back_spec (im := im) w wp
    refine ⟨t, 6, ((su.trans uv).trans vw).trans wt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), wr.get (by simp), v28]
    · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
    · exact (((uf.trans vf).trans wf).trans tf).mono (by intro A hA h; simpa using h)
  · rw [if_neg hz] at vp
    obtain ⟨t, vt, tp, tr, tf⟩ := back_spec (im := im) v vp
    refine ⟨t, 5, (su.trans uv).trans vt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), v28]
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)

theorem finish_spec (s : MachineState) (hpc : s.pc = pcOf 1117) (ret : Nat)
    (hz : remaining s = 0) (hl : s.getReg .x8 ≠ 0) (hra : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 18 18 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec (im := im) s hpc
  have he : remaining u = 0 := by unfold remaining; rw [ur.get (by simp), ur.get (by simp)]; exact hz
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec (im := im) u up
  rw [if_pos he] at vp
  have h8 : v.getReg .x8 ≠ 0 := by rw [vr.get (by simp), ur.get (by simp)]; exact hl
  obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec (im := im) v vp
  rw [if_neg h8] at wp
  obtain ⟨t, wt, tp, m0, m8, m48, m56, tr, tf⟩ := pair_spec (im := im) w wp ret
    (by rw [wr.get (by simp), vr.get (by simp), ur.get (by simp)]; exact hra)
  have fsw : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by intro A hA h; simpa using h)
  refine ⟨t, ((su.trans uv).trans vw).trans wt, tp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, fsw.get (by decide) (by simp)]
  · rw [m8, fsw.get (by decide) (by simp)]
  · rw [m48, fsw.get (by decide) (by simp)]
  · rw [m56, fsw.get (by decide) (by simp)]
  · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
  · exact (fsw.trans tf).mono (by intro A hA h; simpa using h)

end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-- Pairing stage 1: steps of expand's chain header (1032 .. 1040), five fewer than `Keygen.headerK`. -/
def expHdrK (lay : T3.Layer) : Nat := if lay.val = 0 then 25 else if lay.val = 1 then 28 else 29
theorem expHdrK_le (lay : T3.Layer) : expHdrK lay ≤ 29 := by unfold expHdrK; split_ifs <;> omega
class Code (im : Image) : Prop where
  e_hdrA_at : CodeAt im (pcOf 1119) e_hdrA
  e_hdrB_at : CodeAt im (pcOf 42765) e_hdrB
  e_hdrC_at : CodeAt im (pcOf 42768) e_hdrC
  e_hdrD_at : CodeAt im (pcOf 42776) e_hdrD
  e_hdrE_at : CodeAt im (pcOf 1129) e_hdrE
  e_hpA_at : CodeAt im (pcOf 42741) e_hpA
  e_hpZ_at : CodeAt im (pcOf 42755) e_hpZ
  e_kpad_at : CodeAt im (pcOf 49819) e_kpad
  e_kmax0_at : CodeAt im (pcOf 49812) e_kmax0
  e_kmax1_at : CodeAt im (pcOf 49814) e_kmax1
  e_kmax2_at : CodeAt im (pcOf 49817) e_kmax2
  e_kmax3_at : CodeAt im (pcOf 49818) e_kmax3
  e_hpJ_at : CodeAt im (pcOf 42757) e_hpJ
  e_w1009_at : CodeAt im (pcOf 1009) e_w1009
  e_slA_at : CodeAt im (pcOf 42758) e_slA
  e_slB_at : CodeAt im (pcOf 42760) e_slB
  e_slN_at : CodeAt im (pcOf 42761) e_slN
  e_slT_at : CodeAt im (pcOf 42763) e_slT
  e_slZ_at : CodeAt im (pcOf 42764) e_slZ
  codeAt_1010 : CodeAt im (pcOf 1010) seg_1010
  codeAt_1011 : CodeAt im (pcOf 1011) seg_1011
  codeAt_1027 : CodeAt im (pcOf 1027) seg_1027
  codeAt_1028 : CodeAt im (pcOf 1028) seg_1028
  codeAt_1030 : CodeAt im (pcOf 1030) seg_1030
  codeAt_1031 : CodeAt im (pcOf 1031) seg_1031
  -- Pairing stage 1: 1041 `jal 43764` and the G/F chain step block 43764..43789.
  codeAt_1041 : CodeAt im (pcOf 1041) seg_1041
  codeAt_43764 : CodeAt im (pcOf 43764) seg_43764
  codeAt_43766 : CodeAt im (pcOf 43766) seg_43766
  codeAt_43767 : CodeAt im (pcOf 43767) seg_43767
  codeAt_43779 : CodeAt im (pcOf 43779) seg_43779
  codeAt_43780 : CodeAt im (pcOf 43780) seg_43780
  codeAt_43781 : CodeAt im (pcOf 43781) seg_43781
  codeAt_43783 : CodeAt im (pcOf 43783) seg_43783
  codeAt_43788 : CodeAt im (pcOf 43788) seg_43788
  codeAt_43789 : CodeAt im (pcOf 43789) seg_43789
  codeAt_1049 : CodeAt im (pcOf 1049) seg_1049
  codeAt_1052 : CodeAt im (pcOf 1052) seg_1052
  codeAt_1063 : CodeAt im (pcOf 1063) seg_1063
  codeAt_1072 : CodeAt im (pcOf 1072) seg_1072
  codeAt_1073 : CodeAt im (pcOf 1073) seg_1073
  codeAt_1076 : CodeAt im (pcOf 1076) seg_1076
  codeAt_1077 : CodeAt im (pcOf 1077) seg_1077
  codeAt_1080 : CodeAt im (pcOf 1080) seg_1080
  codeAt_1099 : CodeAt im (pcOf 1099) seg_1099
  codeAt_1138 : CodeAt im (pcOf 1138) seg_1138
  codeAt_1139 : CodeAt im (pcOf 1139) seg_1139
  codeAt_1143 : CodeAt im (pcOf 1143) seg_1143
  codeAt_1158 : CodeAt im (pcOf 1158) seg_1158
  codeAt_1160 : CodeAt im (pcOf 1160) seg_1160
  codeAt_997 : CodeAt im (pcOf 997) seg_997
  -- Stage 2 (C2 + C3, #866): the chain tail trampoline (from 1047), the left-child current value trampoline
  -- (from 1103) and the packed lower node word (from 42775); the same words at the same addresses as `image`.
  e_hdrT_at : CodeAt im (pcOf 43467) e_hdrT
  e_ct0_at : CodeAt im (pcOf 43451) e_ct0
  e_ct1_at : CodeAt im (pcOf 43452) e_ct1
  e_ct2_at : CodeAt im (pcOf 43453) e_ct2
  e_ct3_at : CodeAt im (pcOf 43455) e_ct3
  e_ct4_at : CodeAt im (pcOf 43460) e_ct4
  e_lcA_at : CodeAt im (pcOf 43462) e_lcA
  e_lcB_at : CodeAt im (pcOf 43465) e_lcB
  e_lcC_at : CodeAt im (pcOf 43466) e_lcC
  e_lcD_at : CodeAt im (pcOf 1105) e_lcD
variable {im : Image} [Code im]
variable [BCBlocks.Code im] [PackedBlocks.Code im]
variable (s : MachineState)
theorem rl997_spec (hpc : s.pc = pcOf 997) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps im s (hpK lay) (hpK lay) t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      (lay = 0 → TopPadZero t) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24 ∨ TopPadW A) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42741 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_997 (Code.codeAt_997 (im := im)) s hpc (by simp [eblk_997.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_997.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  have g15 : t1.getReg .x15 = BitVec.ofNat 64 (T3.height lay) := by rw [r1.get (by decide), h15]
  obtain ⟨t2, s2, p2, m16, m24, x28, r2, f2⟩ : ∃ t, Steps im t1 14 14 t ∧
      t.pc = (if lay = 0 then pcOf 42755 else pcOf 42757) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧ t.getReg .x28 = BitVec.ofNat 64 LEAFPK ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, symRun_sound eb_hpA (Code.e_hpA_at (im := im)) t1 p1
      (by simp [eb_hpA.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hpA.res, E.eval, CmpOp.eval, g8, bne]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay.val 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0
      · subst h0; simp
      · have : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp [h0, this]
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [g8, g9, g18, g15, LEAFPK]
      have hh : T3.height lay < 64 := by fin_cases lay <;> decide
      rw [Nat.mod_eq_of_lt (by omega : T3.height lay < 18446744073709551616), Nat.mod_eq_of_lt hh,
        show (513#64) = BitVec.ofNat 64 513 from rfl,
        ofNat_or_disjoint 513 ((tree * 2 ^ T3.height lay + leaf) * 65536) 16 (by decide) (by omega),
        ofNat_or_disjoint' _ (↑lay * 281474976710656) 48 (by omega) (by omega),
        show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
        ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
      unfold T3.hyperWord
      congr 1
      rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt (by omega : lay.val < 256)]
      omega
    · simp only [Result.toState_getMem, eb_hpA.res]
      t3n [LEAFPK]
    · simp [eb_hpA.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_hpA.res, rv_simp] <;> rfl
    · intro A hA hn
      simp only [Result.toState_getMem, eb_hpA.res]
      t3n []
      simp only [LEAFPK] at hn
      rw [if_neg (by omega), if_neg (by omega)]
  obtain ⟨t3, s3, p3, z0, zp, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 8 else 1) (if lay = 0 then 8 else 1) t ∧
      t.pc = pcOf 1009 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      (lay = 0 → TopPadZero t) ∧
      RegsExcept t2 t [] ∧ Frame t2 t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ TopPadW A) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      obtain ⟨u, su, pu, ru, fu⟩ : ∃ u, Steps im t2 1 1 u ∧ u.pc = pcOf 49819 ∧ RegsExcept t2 u [] ∧
          Frame t2 u (fun _ => False) := by
        refine ⟨_, symRun_sound eb_hpZ (Code.e_hpZ_at (im := im)) t2 p2 (by simp [eb_hpZ.res, rv_simp]), ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_hpZ.res, E.eval]
        · intro r hr; cases r <;> rfl
        · intro A _ _; rfl
      have u28 : u.getReg .x28 = BitVec.ofNat 64 LEAFPK := by rw [ru.get (by decide), x28]
      refine ⟨_, (su.trans (symRun_sound eb_kpad (Code.e_kpad_at (im := im)) u pu
        (by simp [eb_kpad.res, rv_simp, u28, accessValid_iff, MEMORY_BYTES, LEAFPK]))).of_eq (by simp [h0, eb_kpad.res])
        (by simp [h0, eb_kpad.res]),
        ?_, fun _ => ⟨?_, ?_⟩, fun _ => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp [Result.toState_pc, eb_kpad.res, E.eval]
      all_goals first
        | (simp only [Result.toState_getMem, eb_kpad.res]; t3n [u28, LEAFPK]; done)
        | skip
      · intro r hr; rw [Result.toState_getReg]; rw [← ru.get hr]
        cases r <;> first | rfl | exact (hr (by decide)).elim
      · intro A hA hn
        simp only [Result.toState_getMem, eb_kpad.res]
        t3n [u28]
        simp only [LEAFPK, TopPadW] at hn ⊢
        split_ifs <;> first | (exfalso; omega) | exact fu.get hA (by simp)
    · rw [if_neg h0] at p2
      refine ⟨_, (symRun_sound eb_hpJ (Code.e_hpJ_at (im := im)) t2 p2 (by simp [eb_hpJ.res, rv_simp])).of_eq (by simp [h0, eb_hpJ.res])
        (by simp [h0, eb_hpJ.res]), ?_, fun h => absurd h h0, fun h => absurd h h0, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpJ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
  obtain ⟨t4, s4, p4, x19, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1010 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t3 t [.x19] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_w1009 (Code.e_w1009_at (im := im)) t3 p3 (by simp [eb_w1009.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_w1009.res, E.eval]
    · simp [eb_w1009.res, rv_simp]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_w1009.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_w1009.res, rv_simp]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hpK; split_ifs <;> simp_all)
    (by unfold hpK; split_ifs <;> simp_all), p4, x19, ?_, ?_, fun h => ?_, fun h => ?_,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h <;> simp only [LEAFPK, TopPadW] at h ⊢ <;> omega)⟩
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK, TopPadW]; omega), m16]
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK, TopPadW]; omega), m24]
  · obtain ⟨a, b⟩ := z0 h
    exact ⟨by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), a],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), b]⟩
  · obtain ⟨a, b, c, d⟩ := zp h
    exact ⟨by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), a],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), b],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), c],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), d]⟩

theorem rl1010_spec (hpc : s.pc = pcOf 1010) (i n : Nat) (hi : i < 2 ^ 63) (hn : n < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if n ≤ i then pcOf 1063 else pcOf 1011) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1010 (Code.codeAt_1010 (im := im)) s hpc (by simp [eblk_1010.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1010.res, E.eval, CmpOp.eval, h19, h26]
    rw [ex_slt i n hi hn]
    by_cases hc : n ≤ i
    · simp [hc, show ¬ i < n by omega]
    · simp [hc, show i < n by omega]
  · ex_regs eblk_1010.res
  · intro A _ _; simp [eblk_1010.res, rv_simp]

theorem rl1011_spec (hpc : s.pc = pcOf 1011) (i P W : Nat) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616)
    (hP8 : P % 8 = 0) (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h16 : s.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 W) :
    ∃ t, Steps im s 16 16 t ∧ t.pc = pcOf 1027 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getMem (BitVec.ofNat 64 (W + 48)) = s.getMem (BitVec.ofNat 64 (P + 16 * i)) ∧
      t.getMem (BitVec.ofNat 64 (W + 56)) = s.getMem (BitVec.ofNat 64 (P + 16 * i + 8)) ∧
      t.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ t.getReg .x28 = BitVec.ofNat 64 (i + DIGITS) ∧
      RegsExcept s t [.x6, .x7, .x23, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) := by
  have ea : ∀ k, BitVec.ofNat 64 i <<< ((4#64 : Word).toNat % 64) + BitVec.ofNat 64 P + BitVec.ofNat 64 k =
      BitVec.ofNat 64 (P + 16 * i + k) := fun k => by
    rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, ofNat_shl, ofNat_add_ofNat, ofNat_add_ofNat]
    congr 1; ring
  have hne : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → x ≠ y → BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
    fun x y hx hy h he => h ((ofNat_inj hx hy).mp he)
  have hv : ∀ x : Nat, x % 8 = 0 → x + 8 ≤ 2 ^ 24 → accessValid (BitVec.ofNat 64 x) 8 = true := fun x h1 h2 => by
    rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
  refine ⟨_, symRun_sound eblk_1011 (Code.codeAt_1011 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1011.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, h19, h16, h23,
      ea, ofNat_add_ofNat, show (56#64 : Word) = BitVec.ofNat 64 56 from rfl,
      show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, show (131536#64 : Word) = BitVec.ofNat 64 131536 from rfl,
      show (131544#64 : Word) = BitVec.ofNat 64 131544 from rfl]
    refine ⟨hv _ (by omega) (by omega), hv _ (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hv _ (by omega) (by omega), hv _ (by omega) (by omega)⟩
  · simp [Result.toState_pc, eblk_1011.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eblk_1011.res, CHAIN]
      t3n [h19, h16, h23]
      (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h23]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt (show W < 2 ^ 64 by omega), toNat_ofNat_lt (show W - 64 < 2 ^ 64 by omega)]
    rw [show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1011.res, rv_simp, h19, ofNat_add_ofNat]
  · ex_regs eblk_1011.res
  · intro A hA hn
    simp only [CHAIN] at hn
    simp only [Result.toState_getMem, eblk_1011.res, rv_simp, h23, ofNat_add_ofNat]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem rl1027_spec (hpc : s.pc = pcOf 1027) (i d : Nat) (hi : i < 64) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (i + DIGITS))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1028 ∧ t.getReg .x20 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have ea : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (DIGITS + i) := by
    rw [h28, show signExtend12 (0 : BitVec 12) = 0 from rfl, add_zero, Nat.add_comm]
  have hv : accessValid (s.getReg .x28 + signExtend12 0) 1 = true := by
    rw [ea, accessValid_iff, toNat_ofNat_lt (by simp only [DIGITS]; omega)]; simp only [MEMORY_BYTES, DIGITS]; omega
  refine ⟨_, steps_lbu (Code.codeAt_1027 (im := im)) hpc lbu_word1027 hv, ?_, ?_, ?_, ?_⟩
  · show s.pc + 4 = _; rw [hpc, pcOf_add4]
  · have e2 : ∀ (u : MachineState) (v pc : Word), ((u.setReg .x20 v).setPC pc).getReg .x20 = v :=
      fun u v pc => rfl
    rw [e2, ea, hb]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth]
    omega
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    show ((s.setReg .x20 _).setPC _).getReg r = _
    cases r <;> simp_all [MachineState.getReg, MachineState.setReg, MachineState.setPC]
  · intro A _ _; rfl

theorem rl1028_spec (hpc : s.pc = pcOf 1028) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1030 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt hlay] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound eblk_1028 (Code.codeAt_1028 (im := im)) s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h8, hz]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]

theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 1158 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 (Code.codeAt_1030 (im := im)) s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]

/-- R6 top chain caps (KMAX): 7 for the checksum chain (`i >= s11 = 51`), 4 for the r5 chains, 5 for the r6 chains. -/
def kmaxCap (i n4 : Nat) : Nat := if n4 ≤ i then 7 else if 24 ≤ i then 4 else 5
def kmaxSteps (i n4 : Nat) : Nat := if n4 ≤ i then 4 else if 24 ≤ i then 7 else 8
theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps im s (kmaxSteps i n4) (kmaxSteps i n4) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x21 = BitVec.ofNat 64 (kmaxCap i n4) ∧ RegsExcept s t [.x21, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 49812 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1158 (Code.codeAt_1158 (im := im)) s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1158.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  have g27 : t0.getReg .x27 = BitVec.ofNat 64 n4 := by rw [r0.get (by decide), h27]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 2 2 t ∧
      t.pc = (if i < n4 then pcOf 49814 else pcOf 49818) ∧ t.getReg .x21 = BitVec.ofNat 64 7 ∧
      RegsExcept t0 t [.x21] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax0 (Code.e_kmax0_at (im := im)) t0 p0 (by simp [eb_kmax0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax0.res, E.eval, CmpOp.eval, g19, g27]
      rw [ex_slt i n4 hi hn]
      by_cases hi' : i < n4 <;> simp [hi']
    · simp [eb_kmax0.res, rv_simp]
    · ex_regs eb_kmax0.res
    · intro A _ _; simp [eb_kmax0.res, rv_simp]
  have j3 : ∀ u : MachineState, u.pc = pcOf 49818 → ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf 1031 ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := fun u hu => by
    refine ⟨_, symRun_sound eb_kmax3 (Code.e_kmax3_at (im := im)) u hu (by simp [eb_kmax3.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax3.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  by_cases hin : i < n4
  · rw [if_pos hin] at p1
    have g19' : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), g19]
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
        t.pc = (if i < 24 then pcOf 49817 else pcOf 49818) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
        RegsExcept t1 t [.x21, .x28] ∧ Frame t1 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_kmax1 (Code.e_kmax1_at (im := im)) t1 p1 (by simp [eb_kmax1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp only [Result.toState_pc, eb_kmax1.res, E.eval, CmpOp.eval, g19']
        rw [show (24#64 : Word) = BitVec.ofNat 64 24 from rfl, ex_slt i 24 hi (by norm_num)]
        by_cases hi' : i < 24 <;> simp [hi']
      · simp [eb_kmax1.res, rv_simp]
      · ex_regs eb_kmax1.res
      · intro A _ _; simp [eb_kmax1.res, rv_simp]
    by_cases h24 : i < 24
    · rw [if_pos h24] at p2
      obtain ⟨t3, s3, p3, x3, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧ t.pc = pcOf 1031 ∧
          t.getReg .x21 = BitVec.ofNat 64 5 ∧ RegsExcept t2 t [.x21] ∧ Frame t2 t (fun _ => False) := by
        refine ⟨_, symRun_sound eb_kmax2 (Code.e_kmax2_at (im := im)) t2 p2 (by simp [eb_kmax2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_kmax2.res, E.eval]
        · simp [eb_kmax2.res, rv_simp]
        · ex_regs eb_kmax2.res
        · intro A _ _; simp [eb_kmax2.res, rv_simp]
      refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega) (by unfold kmaxSteps; split_ifs <;> omega),
        p3, by rw [x3, kmaxCap, if_neg (by omega), if_neg (by omega)], (((r0.trans r1).trans r2).trans r3).mono (by decide),
        (((f0.trans f1).trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
    · rw [if_neg h24] at p2
      obtain ⟨t3, s3, p3, r3, f3⟩ := j3 t2 p2
      refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega) (by unfold kmaxSteps; split_ifs <;> omega),
        p3, by rw [r3.get (by decide), x2, kmaxCap, if_neg (by omega), if_pos (by omega)],
        (((r0.trans r1).trans r2).trans r3).mono (by decide),
        (((f0.trans f1).trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  · rw [if_neg hin] at p1
    obtain ⟨t3, s3, p3, r3, f3⟩ := j3 t1 p1
    refine ⟨t3, ((s0.trans s1).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega) (by unfold kmaxSteps; split_ifs <;> omega),
      p3, by rw [r3.get (by decide), x1, kmaxCap, if_pos (by omega)], ((r0.trans r1).trans r3).mono (by decide),
      ((f0.trans f1).trans f3).mono (fun A _ h => by simp_all)⟩

theorem rl1160_spec (hpc : s.pc = pcOf 1160) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1160 (Code.codeAt_1160 (im := im)) s hpc (by simp [eblk_1160.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1160.res, E.eval]
  · simp [eblk_1160.res, rv_simp]
  · ex_regs eblk_1160.res
  · intro A _ _; simp [eblk_1160.res, rv_simp]

theorem rl1031_spec (hpc : s.pc = pcOf 1031) (st e : Nat) (hs : st < 2 ^ 63) (he : e < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if e ≤ st then pcOf 1049 else pcOf 1032) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1031 (Code.codeAt_1031 (im := im)) s hpc (by simp [eblk_1031.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1031.res, E.eval, CmpOp.eval, h20, h21]
    rw [ex_slt st e hs he]
    by_cases hc : e ≤ st
    · simp [hc, show ¬ st < e by omega]
    · simp [hc, show st < e by omega]
  · ex_regs eblk_1031.res
  · intro A _ _; simp [eblk_1031.res, rv_simp]

theorem rl1032_spec (hpc : s.pc = pcOf 1032) (lay : T3.Layer) (tree leaf i st : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay)
    (hi : i < 64) (hs : st < 8)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h9 : s.getReg .x9 = BitVec.ofNat 64 tree) (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧ t.pc = pcOf 1041 ∧
      t.getReg .x28 = BitVec.ofNat 64 CHAIN ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (T3.chainHeader lay tree leaf i st).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := by
  have run : ∃ t, Steps im s (expHdrK lay) (expHdrK lay) t ∧
      t.pc = pcOf 1041 ∧ PackedBlocks.ExpHeaderPost s t (T3.height lay) := by
    fin_cases lay
    · exact PackedBlocks.expand_header_0 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_1 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_2 (im := im) s hpc h8
    · exact PackedBlocks.expand_header_3 (im := im) s hpc h8
  obtain ⟨t, steps, pc, post⟩ := run
  refine ⟨t, steps, pc, post.x28,
    post.low.trans (Keygen.PackedBlocks.packedAt_source s lay tree leaf i st hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (Keygen.PackedBlocks.routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi hs).symm

/-- Pairing stage 1: the F path's C3 tail `jal 43451` (at 43789) and its trampoline (an F chain: `isG = false`). -/
theorem rl1047_spec (hpc : s.pc = pcOf 43789) (lay : T3.Layer) (i m : Nat) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
    (hG : ClaudeWCT.WCT9.isG lay i = false)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (lo hv : T3.Digest) (hlo : DigAt s (CHAIN + 48) lo)
    (hhv : DigAt s (CHAIN + 64) hv) :
    ∃ t, Steps im s (2 + trXE lay.val i m) (2 + trXE lay.val i m) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      DigAt t (CHAIN + 48) (if ClaudeWCT.WCT9.chainHigh lay i m then hv else lo) ∧
      RegsExcept s t [.x6, .x7, .x20, .x28] ∧ Frame s t (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
  have hlay : lay.val < 2 ^ 64 := by have := lay.isLt; omega
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43451 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_43789 (Code.codeAt_43789 (im := im)) s hpc (by simp [eblk_43789.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_43789.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have last : ∀ u : MachineState, u.pc = pcOf 43460 → u.getReg .x20 = BitVec.ofNat 64 m →
      ∃ t, Steps im u 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
        RegsExcept u t [.x20] ∧ Frame u t (fun _ => False) := by
    intro u hu hu20
    refine ⟨_, symRun_sound eb_ct4 (Code.e_ct4_at (im := im)) u hu (by simp [eb_ct4.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [eb_ct4.res, E.eval]
    · simp only [Result.toState_getReg, eb_ct4.res, rv_simp, hu20]
      rw [ofNat_add_ofNat]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct4.res, rv_simp] <;> rfl
    · intro A _ _; simp [eb_ct4.res, rv_simp]
  have ne_of {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
      (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
    by_cases hxy : x = y
    · subst hxy; simp
    · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
      simp [hxy, this]
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im t0 1 1 t ∧ t.pc = (if i ≠ 0 then pcOf 43460 else pcOf 43452) ∧
      RegsExcept t0 t [] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct0 (Code.e_ct0_at (im := im)) t0 p0 (by simp [eb_ct0.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct0.res, E.eval, CmpOp.eval, r0.get (by simp), h19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ne_of hi (by norm_num)]
      by_cases hi0 : i = 0 <;> simp [hi0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g1 : ∀ r, r ∉ ([] : List Reg) → t1.getReg r = s.getReg r := fun r hr => (r0.trans r1).get hr
  by_cases hi0 : i ≠ 0
  · rw [if_pos hi0] at p1
    obtain ⟨t2, s2, p2, x2, r2, f2⟩ := last t1 p1 (by rw [g1 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inl hi0)
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by simp [trXE, hi0]) (by simp [trXE, hi0]), p2, x2, ?_,
      ((r0.trans r1).trans r2).mono (by simp), ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame ((f0.trans f1).trans f2) (by decide) (by simp) (by simp)
  have hi0' : i = 0 := by omega
  rw [if_neg hi0] at p1
  obtain ⟨t2, s2, p2, r2, f2⟩ : ∃ t, Steps im t1 1 1 t ∧
      t.pc = (if lay.val = 0 then pcOf 43460 else pcOf 43453) ∧
      RegsExcept t1 t [] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct1 (Code.e_ct1_at (im := im)) t1 p1 (by simp [eb_ct1.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct1.res, E.eval, CmpOp.eval, g1 _ (by simp), h8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ _ hlay (by norm_num)]
      by_cases hl0 : lay.val = 0 <;> simp [hl0]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g2 : ∀ r, r ∉ ([] : List Reg) → t2.getReg r = s.getReg r := fun r hr => ((r0.trans r1).trans r2).get hr
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ hA => by simp_all)
  by_cases hl0 : lay.val = 0
  · rw [if_pos hl0] at p2
    obtain ⟨t3, s3, p3, x3, r3, f3⟩ := last t2 p2 (by rw [g2 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false :=
      ClaudeWCT.WCT9.chainHigh_eq_false (Or.inl (Fin.ext hl0))
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by simp [trXE, hi0', hl0]) (by simp [trXE, hi0', hl0]),
      p3, x3, ?_, (((r0.trans r1).trans r2).trans r3).mono (by simp),
      (f02.trans f3).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f02.trans f3) (by decide) (by simp) (by simp)
  rw [if_neg hl0] at p2
  obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧ t.pc = (if m ≠ 6 then pcOf 43460 else pcOf 43455) ∧
      RegsExcept t2 t [.x6] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_ct2 (Code.e_ct2_at (im := im)) t2 p2 (by simp [eb_ct2.res, rv_simp]), ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_ct2.res, E.eval, CmpOp.eval, g2 _ (by simp), h20]
      rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, ne_of (by omega) (by norm_num)]
      by_cases hm6 : m = 6 <;> simp [hm6]
    · intro r hr; simp at hr; cases r <;> simp_all [eb_ct2.res, rv_simp] <;> rfl
    · intro A hA hn; simp [eb_ct2.res, rv_simp]
  have f03 : Frame s t3 (fun _ => False) := (f02.trans f3).mono (fun A _ hA => by simp_all)
  have g3 : ∀ r, r ∉ [.x6] → t3.getReg r = s.getReg r := fun r hr => ((((r0.trans r1).trans r2).trans r3)).get
    (by simpa using hr)
  by_cases hm6 : m ≠ 6
  · rw [if_pos hm6] at p3
    obtain ⟨t4, s4, p4, x4, r4, f4⟩ := last t3 p3 (by rw [g3 _ (by simp)]; exact h20)
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false :=
      ClaudeWCT.WCT9.chainHigh_eq_false_F hG (Or.inr hm6)
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by simp [trXE, hi0', hl0, hm6])
      (by simp [trXE, hi0', hl0, hm6]), p4, x4, ?_, ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by simp),
      (f03.trans f4).mono (fun A _ hA => by simp_all)⟩
    rw [hs]
    exact hlo.frame (f03.trans f4) (by decide) (by simp) (by simp)
  have hm6' : m = 6 := by omega
  rw [if_neg hm6] at p3
  have hs : ClaudeWCT.WCT9.chainHigh lay i m = true :=
    ClaudeWCT.WCT9.chainHigh_eq_true.mpr ⟨fun h => hl0 (by rw [h]; rfl), Or.inl ⟨hi0', hm6'⟩⟩
  have hobl : Oblig.all t3 eb_ct3.res.st.obl := by simp [eb_ct3.res, rv_simp]
  refine ⟨_, ((((s0.trans s1).trans s2).trans s3).trans (symRun_sound eb_ct3 (Code.e_ct3_at (im := im)) t3 p3 hobl)).of_eq
    (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]) (by simp [trXE, hi0', hl0, hm6', eb_ct3.res]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [eb_ct3.res, E.eval]
  · simp only [Result.toState_getReg, eb_ct3.res, rv_simp]
    rw [g3 .x20 (by simp), h20, hm6']; rfl
  · rw [hs, if_pos rfl]
    have hv3 := hhv.frame f03 (by decide) (by simp) (by simp)
    constructor
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.1
    · simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      exact hv3.2
  · exact ((((r0.trans r1).trans r2).trans r3).trans (eb_ct3_regs t3)).mono (by simp)
  · have f4 : Frame t3 (eb_ct3.res.toState t3) (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56) := by
      intro A hA hn
      simp only [Result.toState_getMem, eb_ct3.res]
      t3n []
      have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
      rw [hA', if_neg (by simp only [CHAIN] at hn; omega), if_neg (by simp only [CHAIN] at hn; omega)]
    exact (f03.trans f4).mono (fun A _ hA => by simp_all)

/-! ### Pairing stage 1: the chain step block 43764..43789 (ported from the sign `PairStep` block 1732..1757) -/
theorem pe_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem pe_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x == BitVec.ofNat 64 y) = decide (x = y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
theorem pe_and1 (x : Nat) : BitVec.ofNat 64 x &&& 1#64 = BitVec.ofNat 64 (x % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (1 : Nat) % 2 ^ 64 = 1 by norm_num, Nat.and_one_is_mod]
  omega

/-- 1041 `jal 43764`, 43764 `andi t1,s3,1`, 43765 `beq s0,zero,43783`. -/
theorem sel_spec (hpc : s.pc = pcOf 1041) (lay i : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if lay = 0 then pcOf 43783 else pcOf 43766) ∧
      t.getReg .x6 = BitVec.ofNat 64 (i % 2) ∧ RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 43764 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1041 (Code.codeAt_1041 (im := im)) s hpc (by simp [eblk_1041.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_1041.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  refine ⟨_, s0.trans (symRun_sound eblk_43764 (Code.codeAt_43764 (im := im)) t0 p0
    (by simp [eblk_43764.res, rv_simp])), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_43764.res, E.eval, CmpOp.eval, r0.get (by simp), h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq hlay (by norm_num)]
    by_cases hl0 : lay = 0 <;> simp [hl0]
  · simp only [Result.toState_getReg, eblk_43764.res, rv_simp, r0.get (show Reg.x19 ∉ ([] : List Reg) by simp), h19]
    exact pe_and1 i
  · have r1 : RegsExcept t0 (eblk_43764.res.toState t0) [.x6] := by
      intro r hr; simp at hr; cases r <;> simp_all [eblk_43764.res, rv_simp] <;> rfl
    exact (r0.trans r1).mono (by simp)
  · have f1 : Frame t0 (eblk_43764.res.toState t0) (fun _ => False) := by
      intro A _ _; simp [eblk_43764.res, rv_simp]
    exact (f0.trans f1).mono (fun A _ h => by simp_all)

/-- 43766 `beq t1,zero,43783`. -/
theorem gsel_spec (hpc : s.pc = pcOf 43766) (i : Nat) (h6 : s.getReg .x6 = BitVec.ofNat 64 (i % 2)) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if i % 2 = 0 then pcOf 43783 else pcOf 43767) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_43766 (Code.codeAt_43766 (im := im)) s hpc (by simp [eblk_43766.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_43766.res, E.eval, CmpOp.eval, h6]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; cases r <;> rfl
  · intro A hA hn; rfl

/-- The G body 43767..43778 (and 43779 at step 6): pads, header copy, HASH arguments. -/
theorem g_spec (hpc : s.pc = pcOf 43767) (m : Nat)
    (hm : m < 2 ^ 63) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (12 + (if m = 6 then 1 else 0)) (12 + (if m = 6 then 1 else 0)) t ∧ t.pc = pcOf 43780 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = 6 then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s eblk_43767.res.st.obl := by
    simp only [eblk_43767.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  have st := symRun_sound eblk_43767 (Code.codeAt_43767 (im := im)) s hpc hobl
  set u := eblk_43767.res.toState s with hu
  have upc : u.pc = (if m = 6 then pcOf 43779 else pcOf 43780) := by
    simp only [hu, Result.toState_pc, eblk_43767.res, E.eval, CmpOp.eval, h20]
    rw [show (6#64 : Word) = BitVec.ofNat 64 6 from rfl, pe_ne (by omega) (by norm_num)]
    by_cases hm6 : m = 6 <;> simp [hm6]
  have ur : RegsExcept s u [.x6, .x10, .x11, .x12] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, eblk_43767.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    simp only [hu, Result.toState_getMem, eblk_43767.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131560 by omega, show ¬ A = 131568 by omega, show ¬ A = 131576 by omega,
      show ¬ A = 131584 by omega, show ¬ A = 131592 by omega, show ¬ A = 131552 by omega, if_false]
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, eblk_43767.res, rv_simp, h28] <;> rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, eblk_43767.res, rv_simp] <;> rfl
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, eblk_43767.res, rv_simp, h28] <;> rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, eblk_43767.res]
      t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  by_cases hm6 : m = 6
  · rw [if_pos hm6] at upc
    have hobl6 : Oblig.all u eblk_43779.res.st.obl := by simp [eblk_43779.res, rv_simp]
    have st6 := symRun_sound eblk_43779 (Code.codeAt_43779 (im := im)) u upc hobl6
    refine ⟨_, (st.trans st6).of_eq (by simp [hm6, eblk_43767.res, eblk_43779.res])
      (by simp [hm6, eblk_43767.res, eblk_43779.res]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [eblk_43779.res, E.eval]
    · simp only [Result.toState_getReg, eblk_43779.res, rv_simp]; exact u10
    · simp only [Result.toState_getReg, eblk_43779.res, rv_simp]; exact u11
    · simp only [Result.toState_getReg, eblk_43779.res, rv_simp, if_pos hm6, ur.get (show Reg.x28 ∉ _ by simp), h28]
      rfl
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.1
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.2.1
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.2.2.1
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.2.2.2.1
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.2.2.2.2.1
    · simp only [Result.toState_getMem, eblk_43779.res, rv_simp]; exact umem.2.2.2.2.2
    · intro r hr
      rw [show (eblk_43779.res.toState u).getReg r = u.getReg r by
        cases r <;> simp_all [eblk_43779.res, rv_simp] <;> rfl]
      exact ur r hr
    · intro A hA hn
      rw [show (eblk_43779.res.toState u).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) by
        simp [eblk_43779.res, rv_simp]]
      exact uf A hA hn
  · rw [if_neg hm6] at upc
    refine ⟨u, st.of_eq (by simp [hm6, eblk_43767.res]) (by simp [hm6, eblk_43767.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg hm6]; exact u12

/-- The F body 43783..43787: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec (hpc : s.pc = pcOf 43783) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 43788 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s eblk_43783.res.st.obl := by
    simp only [eblk_43783.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  refine ⟨_, symRun_sound eblk_43783 (Code.codeAt_43783 (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_43783.res, E.eval]
  · simp only [Result.toState_getReg, eblk_43783.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getReg, eblk_43783.res, rv_simp] <;> rfl
  · simp only [Result.toState_getReg, eblk_43783.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getMem, eblk_43783.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · simp only [Result.toState_getMem, eblk_43783.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_43783.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_43783.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131520 by omega, show ¬ A = 131528 by omega, if_false]

/-- 43781 `addi s4,s4,1`, 43782 `jal 1031`. -/
theorem gtail_spec (hpc : s.pc = pcOf 43781) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_43781 (Code.codeAt_43781 (im := im)) s hpc (by simp [eblk_43781.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [eblk_43781.res, E.eval]
  · simp only [Result.toState_getReg, eblk_43781.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_43781.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_43781.res, rv_simp]

theorem rl1049_spec (hpc : s.pc = pcOf 1049) (lay : T3.Layer) (i : Nat) (hi : i < 2 ^ 59)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (slK lay i) (slK lay i) t ∧ t.pc = pcOf 1052 ∧
      t.getReg .x28 = BitVec.ofNat 64 (slotOff lay i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42758 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1049 (Code.codeAt_1049 (im := im)) s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1049.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g19 : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), h19]
  obtain ⟨t2, s2, p2, x28, r2, f2⟩ : ∃ t, Steps im t1 2 2 t ∧
      t.pc = (if lay = 0 then pcOf 42763 else pcOf 42760) ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧
      RegsExcept t1 t [.x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slA (Code.e_slA_at (im := im)) t1 p1 (by simp [eb_slA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_slA.res, E.eval, CmpOp.eval, g8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay.val 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0
      · subst h0; simp
      · have : lay.val ≠ 0 := fun h => h0 (Fin.ext h)
        simp [h0, this]
    · simp only [Result.toState_getReg, eb_slA.res, rv_simp, g19]
      t3n []; congr 1; ring
    · ex_regs eb_slA.res
    · intro A _ _; simp [eb_slA.res, rv_simp]
  by_cases h0 : lay = 0
  · rw [if_pos h0] at p2
    obtain ⟨t3, s3, p3, y28, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧ t.pc = pcOf 1052 ∧
        t.getReg .x28 = BitVec.ofNat 64 (16 * i + 64) ∧ RegsExcept t2 t [.x28] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slT (Code.e_slT_at (im := im)) t2 p2 (by simp [eb_slT.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slT.res, E.eval]
      · simp only [Result.toState_getReg, eb_slT.res, rv_simp, x28, ofNat_add_ofNat]
      · ex_regs eb_slT.res
      · intro A _ _; simp [eb_slT.res, rv_simp]
    refine ⟨t3, ((s1.trans s2).trans s3).of_eq (by simp [slK, h0]) (by simp [slK, h0]), p3,
      by rw [y28, slotOff, if_pos h0], ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  · rw [if_neg h0] at p2
    have g19' : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19]
    obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps im t2 1 1 t ∧
        t.pc = (if i = 0 then pcOf 42764 else pcOf 42761) ∧ RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slB (Code.e_slB_at (im := im)) t2 p2 (by simp [eb_slB.res, rv_simp]), ?_, ?_, ?_⟩
      · simp only [Result.toState_pc, eb_slB.res, E.eval, CmpOp.eval, g19']
        rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq i 0 (by omega) (by norm_num)]
        by_cases hc : i = 0 <;> simp [hc]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    by_cases hi0 : i = 0
    · rw [if_pos hi0] at p3
      obtain ⟨t4, s4, p4, r4, f4⟩ : ∃ t, Steps im t3 1 1 t ∧ t.pc = pcOf 1052 ∧ RegsExcept t3 t [] ∧
          Frame t3 t (fun _ => False) := by
        refine ⟨_, symRun_sound eb_slZ (Code.e_slZ_at (im := im)) t3 p3 (by simp [eb_slZ.res, rv_simp]), ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_slZ.res, E.eval]
        · intro r hr; cases r <;> rfl
        · intro A hA hn; rfl
      refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, h0, hi0]) (by simp [slK, h0, hi0]), p4,
        by rw [r4.get (by decide), r3.get (by decide), x28, slotOff, if_neg h0, if_pos hi0, hi0],
        (((r1.trans r2).trans r3).trans r4).mono (by decide),
        (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
    · rw [if_neg hi0] at p3
      have y28 : t3.getReg .x28 = BitVec.ofNat 64 (16 * i) := by rw [r3.get (by decide), x28]
      obtain ⟨t4, s4, p4, z28, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1052 ∧
          t.getReg .x28 = BitVec.ofNat 64 (16 * i + 16) ∧ RegsExcept t3 t [.x28] ∧ Frame t3 t (fun _ => False) := by
        refine ⟨_, symRun_sound eb_slN (Code.e_slN_at (im := im)) t3 p3 (by simp [eb_slN.res, rv_simp]), ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_slN.res, E.eval]
        · simp only [Result.toState_getReg, eb_slN.res, rv_simp, y28, ofNat_add_ofNat]
        · ex_regs eb_slN.res
        · intro A _ _; simp [eb_slN.res, rv_simp]
      refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, h0, hi0]) (by simp [slK, h0, hi0]), p4,
        by rw [z28, slotOff, if_neg h0, if_neg hi0], (((r1.trans r2).trans r3).trans r4).mono (by decide),
        (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1052_spec (hpc : s.pc = pcOf 1052) (i x : Nat) (hx8 : x % 8 = 0) (hx : LEAFPK + x + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 x) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 11 11 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + x ∨ A = LEAFPK + x + 8) := by
  refine ⟨_, symRun_sound eblk_1052 (Code.codeAt_1052 (im := im)) s hpc (by
      simp only [eblk_1052.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, h28, ofNat_add_ofNat,
        show (132616#64 : Word) = BitVec.ofNat 64 132616 from rfl,
        show (132608#64 : Word) = BitVec.ofNat 64 132608 from rfl, accessValid_iff, MEMORY_BYTES,
        toNat_ofNat_lt (show x + 132616 < 2 ^ 64 by simp only [LEAFPK] at hx; omega),
        toNat_ofNat_lt (show x + 132608 < 2 ^ 64 by simp only [LEAFPK] at hx; omega)]
      simp only [LEAFPK] at hx; omega), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1052.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1052.res, rv_simp, h19, ofNat_add_ofNat]
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · simp only [Result.toState_getMem, eblk_1052.res, LEAFPK, CHAIN]
    t3n [h28]
    (try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl
  · ex_regs eblk_1052.res
  · intro A hA hn
    simp only [LEAFPK] at hn
    simp only [Result.toState_getMem, eblk_1052.res]
    t3n [h28]
    rw [if_neg (by omega), if_neg (by omega)]

theorem rl1063_spec (hpc : s.pc = pcOf 1063) (n : Nat) (hn : n < 2 ^ 32)
    (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf 1072 ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1063 (Code.codeAt_1063 (im := im)) s hpc (by simp [eblk_1063.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1063.res, E.eval]
  · simp [eblk_1063.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1063.res, rv_simp, h26]
    have e1 : (BitVec.ofNat 64 n + 1#64) <<< ((4#64 : Word).toNat % 64) + 63#64 =
        BitVec.ofNat 64 (16 * (n + 1) + 63) := by
      rw [show ((4#64 : Word).toNat % 64) = 4 from rfl, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
        show (63#64 : Word) = BitVec.ofNat 64 63 from rfl, ofNat_add_ofNat, ofNat_shl, ofNat_add_ofNat]
      congr 1; ring
    rw [e1]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, toNat_ofNat_lt (show 16 * (n + 1) + 63 < 2 ^ 64 by omega),
      toNat_ofNat_lt (show (16 * (n + 1) + 63) / 64 * 64 < 2 ^ 64 by omega),
      show (18446744073709551552#64 : Word).toNat = (2 ^ 58 - 1) * 2 ^ 6 from rfl]
    have key : ∀ x : Nat, x < 2 ^ 64 → x &&& ((2 ^ 58 - 1) * 2 ^ 6) = x / 64 * 64 := by
      intro x hx
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_mul_two_pow, show (64 : Nat) = 2 ^ 6 from rfl, Nat.testBit_mul_two_pow,
        Nat.testBit_two_pow_sub_one]
      by_cases hk : 6 ≤ k
      · simp only [hk, decide_true, Bool.true_and, Nat.testBit_div_two_pow]
        by_cases hk2 : k - 6 < 58
        · simp [hk2, show k - 6 + 6 = k by omega]
        · simp only [hk2, decide_false, Bool.and_false]
          rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      · simp [hk]
    exact key _ (by omega)
  · simp [eblk_1063.res, rv_simp]
  · ex_regs eblk_1063.res
  · intro A _ _; simp [eblk_1063.res, rv_simp]

theorem rl1073_spec (hpc : s.pc = pcOf 1073) (P n : Nat) (hP : P + 16 * n < 2 ^ 64)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 P) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 (P + 16 * n) ∧ RegsExcept s t [.x20, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1073 (Code.codeAt_1073 (im := im)) s hpc (by simp [eblk_1073.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1073.res, E.eval]
  · simp [eblk_1073.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1073.res, rv_simp, h16, h26]
    t3n []; congr 1; ring
  · ex_regs eblk_1073.res
  · intro A _ _; simp [eblk_1073.res, rv_simp]

theorem rl1076_spec (hpc : s.pc = pcOf 1076) (j hh : Nat) (hj : j < 2 ^ 63) (hh' : hh < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = (if hh ≤ j then pcOf 1143 else pcOf 1077) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1076 (Code.codeAt_1076 (im := im)) s hpc (by simp [eblk_1076.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1076.res, E.eval, CmpOp.eval, h20, h15]
    rw [ex_slt j hh hj hh']
    by_cases hc : hh ≤ j
    · simp [hc, show ¬ j < hh by omega]
    · simp [hc, show j < hh by omega]
  · ex_regs eblk_1076.res
  · intro A _ _; simp [eblk_1076.res, rv_simp]

theorem rl1077_spec (hpc : s.pc = pcOf 1077) (leaf j : Nat) (hl : leaf < 2 ^ 64) (hj : j < 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if leaf / 2 ^ j % 2 = 0 then pcOf 1099 else pcOf 1080) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1077 (Code.codeAt_1077 (im := im)) s hpc (by simp [eblk_1077.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1077.res, E.eval, CmpOp.eval, BinOp.eval, h18, h20]
    rw [toNat_ofNat_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj, ofNat_shr _ _ hl, ofNat_and1,
      show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ 0 (by omega) (by norm_num)]
    by_cases hc : leaf / 2 ^ j % 2 = 0
    · simp [hc]
    · simp [hc]
  · ex_regs eblk_1077.res
  · intro A _ _; simp [eblk_1077.res, rv_simp]

theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 19 19 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 M) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M ∨ A = M + 8 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1080 (Code.codeAt_1080 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1080.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | (simp only [show (131584 : Nat) = NODE from rfl, show (131592 : Nat) = NODE + 8 from rfl]; exact ex_ne _ _ (by omega) (by omega) (by omega))
        | skip
  · simp [Result.toState_pc, eblk_1080.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1080.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1080.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1080.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem rl1105_spec (hpc : s.pc = pcOf 1105) (X P : Nat) (hX : X = NOUT ∨ X = NOUT + 16) (hP8 : P % 8 = 0)
    (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (h29 : s.getReg .x29 = BitVec.ofNat 64 X) (h22 : s.getReg .x22 = BitVec.ofNat 64 P) :
    ∃ t, Steps im s 12 12 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 X) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (X + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x30] ∧
      Frame s t (fun A => A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  have hX' : 131648 ≤ X ∧ X ≤ 131664 ∧ X % 8 = 0 := by rcases hX with h | h <;> rw [h] <;> decide
  refine ⟨_, symRun_sound eb_lcD (Code.e_lcD_at (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eb_lcD.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h29, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    repeat' apply And.intro
    all_goals first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
        | skip
  · simp [Result.toState_pc, eb_lcD.res, E.eval]
  iterate 4
    · simp only [Result.toState_getMem, eb_lcD.res, NODE, NOUT]
      t3n [h22, h29]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eb_lcD.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eb_lcD.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
/-- C2 (FULL): the bit-0 branch (current value = left input). Lower layers read the high half of the node output
(`NOUT + 16`, trampoline at 43462), the top layer the low half. -/
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P)
    (hP' : P + 16 ≤ 0x7000 + 5616) (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps im s 22 22 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + hiOff lay + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M + 48 ∨ A = M + 56 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  obtain ⟨t1, s1, p1, m48, m56, r1, f1⟩ : ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 43462 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun A => A = M + 48 ∨ A = M + 56) := by
    refine ⟨_, symRun_sound eblk_1099 (Code.codeAt_1099 (im := im)) s hpc ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [eblk_1099.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
        h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
      repeat' apply And.intro
      all_goals first
          | exact ex_valid _ (by omega) (by omega)
          | exact ex_ne _ _ (by omega) (by omega) (by omega)
          | skip
    · simp [Result.toState_pc, eblk_1099.res, E.eval]
    iterate 2
      · simp only [Result.toState_getMem, eblk_1099.res]
        t3n [h22, h24]
        all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
    · ex_regs eblk_1099.res
    · intro A hA hn
      simp only [Result.toState_getMem, eblk_1099.res]
      t3n [h24]
      rw [if_neg (by omega), if_neg (by omega)]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  obtain ⟨t2, s2, p2, x29, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = pcOf 43465 ∧ t.getReg .x29 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t1 t [.x29] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcA (Code.e_lcA_at (im := im)) t1 p1 (by simp [eb_lcA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcA.res, E.eval]
    · simp [eb_lcA.res, rv_simp]
    · ex_regs eb_lcA.res
    · intro A _ _; simp [eb_lcA.res, rv_simp]
  obtain ⟨t3, s3, p3, y29, r3, f3⟩ : ∃ t, Steps im t2 2 2 t ∧
      t.pc = pcOf 1105 ∧ t.getReg .x29 = BitVec.ofNat 64 (NOUT + hiOff lay) ∧
      RegsExcept t2 t [.x29] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_lcB (Code.e_lcB_at (im := im)) t2 p2 (by simp [eb_lcB.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_lcB.res, E.eval]
    · simp only [Result.toState_getReg, eb_lcB.res, rv_simp, x29, hiOff, ofNat_add_ofNat]
    · ex_regs eb_lcB.res
    · intro A _ _; simp [eb_lcB.res, rv_simp]
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 P := by
    rw [r3.get (by decide), r2.get (by decide), r1.get (by decide), h22]
  obtain ⟨t4, s4, p4, n0, n8, n48, n56, r4, f4⟩ := rl1105_spec (im := im) t3 p3 (NOUT + hiOff lay) P
    (by unfold hiOff; simp) hP8 hP hP' y29 g22
  have f13 : Frame s t3 (fun A => A = M + 48 ∨ A = M + 56) :=
    ((f1.trans f2).trans f3).mono (fun A _ h => by rcases h with (h | h) | h; exact h; exact h.elim; exact h.elim)
  have hoff : hiOff lay ≤ 16 := by unfold hiOff; omega
  refine ⟨t4, ((s1.trans s2).trans s3).trans s4 |>.of_eq rfl rfl, p4,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m48]
  · rw [f4.get (by omega) (by simp only [NODE]; omega), f3.get (by omega) (by simp), f2.get (by omega) (by simp), m56]
  · rw [n0, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n8, f13.get (by simp only [NOUT]; omega) (by simp only [NOUT]; omega)]
  · rw [n48, f13.get (by omega) (by omega)]
  · rw [n56, f13.get (by omega) (by omega)]
  · exact (((r1.trans r2).trans r3).trans r4).mono (by decide)
  · exact (f13.trans f4).mono (fun A _ h => by rcases h with (h | h) | h <;> simp_all)
theorem rl1119_spec (hpc : s.pc = pcOf 1119) (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12) (htopl : lay = 0 → leaf < 2 ^ hh)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (hh - j - 1)) :
    ∃ t, Steps im s (hdrK lay) (hdrK lay) t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        (ClaudeWCT.WCT9.merkleTweak lay tree (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1))).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  set heap := 2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1) with hheap
  have hheap' : heap < 2 ^ 64 := by
    have : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : leaf / 2 ^ (j + 1) ≤ leaf := Nat.div_le_self _ _
    omega
  obtain ⟨t1, s1, p1, x13, r1, f1⟩ : ∃ t, Steps im s 6 6 t ∧ t.pc = pcOf 42765 ∧
      t.getReg .x13 = BitVec.ofNat 64 heap ∧
      RegsExcept s t [.x13, .x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrA (Code.e_hdrA_at (im := im)) s hpc (by simp [eb_hdrA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrA.res, E.eval]
    · simp only [Result.toState_getReg, eb_hdrA.res]
      t3n [h9, h15, h20, h18, h28]
      have e1 : (BitVec.ofNat 64 (hh - j - 1)).toNat % 64 = hh - j - 1 := by
        rw [toNat_ofNat_lt (show hh - j - 1 < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
      simp only [BitVec.toNat_ofNat] at e1
      have e2 : (j + 1) % 18446744073709551616 % 64 = j + 1 := by omega
      have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hq : leaf / 2 ^ (j + 1) < 2 ^ 32 := lt_of_le_of_lt (Nat.div_le_self _ _) hl
      rw [e1, e2, ofNat_shr _ _ (by omega), Nat.one_mul, ofNat_add_ofNat]
    · ex_regs eb_hdrA.res
    · intro A _ _; simp [eb_hdrA.res, rv_simp]
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  obtain ⟨t2, s2, p2, x7, x6, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if lay = 0 then pcOf 42776 else pcOf 42768) ∧
      t.getReg .x7 = 0 ∧
      t.getReg .x6 = BitVec.ofNat 64 heap ∧ RegsExcept t1 t [.x6, .x7] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrB (Code.e_hdrB_at (im := im)) t1 p1 (by simp [eb_hdrB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hdrB.res, E.eval, CmpOp.eval, g8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0 <;> simp [h0]
    · simp [eb_hdrB.res, rv_simp]
    · simp only [Result.toState_getReg, eb_hdrB.res, rv_simp, x13]
    · ex_regs eb_hdrB.res
    · intro A _ _; simp [eb_hdrB.res, rv_simp]
  have g13 : t2.getReg .x13 = BitVec.ofNat 64 heap := by rw [r2.get (by decide), x13]
  obtain ⟨t3, s3, p3, y6, y7, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 1 else 13) (if lay = 0 then 1 else 13) t ∧
      t.pc = pcOf 1129 ∧ t.getReg .x6 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getReg .x7 = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      RegsExcept t2 t [.x6, .x7, .x30] ∧ Frame t2 t (fun _ => False) := by
    by_cases h0 : lay = 0
    · subst h0
      rw [if_pos rfl] at p2
      have hlf := htopl rfl
      have hheap1 : 1 ≤ heap := by
        rw [hheap]; exact le_trans Nat.one_le_two_pow (Nat.le_add_right _ _)
      have hheap2 : heap < 4096 := by
        have e : 2 ^ hh = 2 ^ (j + 1) * 2 ^ (hh - j - 1) := by rw [← Nat.pow_add]; congr 1; omega
        have hq : leaf / 2 ^ (j + 1) < 2 ^ (hh - j - 1) := by
          rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), Nat.mul_comm, ← e]; exact hlf
        have hp : 2 ^ (hh - j - 1) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h11 : (2 : Nat) ^ 11 = 2048 := by norm_num
        rw [hheap]
        rw [h11] at hp
        generalize 2 ^ (hh - j - 1) = X at hq hp ⊢
        generalize leaf / 2 ^ (j + 1) = Y at hq ⊢
        omega
      obtain ⟨wlo, whi⟩ := merkleTweak_words_top tree heap hheap1 hheap2
      refine ⟨_, (symRun_sound eb_hdrD (Code.e_hdrD_at (im := im)) t2 p2 (by simp [eb_hdrD.res, rv_simp])).of_eq (by simp [eb_hdrD.res])
        (by simp [eb_hdrD.res]), ?_, ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hdrD.res, E.eval]
      · rw [wlo]; simp only [Result.toState_getReg, eb_hdrD.res, rv_simp, x6]
      · rw [whi]; simp only [Result.toState_getReg, eb_hdrD.res, rv_simp, x7]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    · rw [if_neg h0] at p2
      have g8' : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [r2.get (by decide), g8]
      have g9' : t2.getReg .x9 = BitVec.ofNat 64 tree := by rw [r2.get (by decide), g9]
      obtain ⟨u, su, pu, uor, u13, ru, fu⟩ : ∃ u, Steps im t2 8 8 u ∧ u.pc = pcOf 43467 ∧
          (u.getReg .x6 ||| u.getReg .x30) = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
          u.getReg .x13 = BitVec.ofNat 64 heap ∧ RegsExcept t2 u [.x6, .x30] ∧ Frame t2 u (fun _ => False) := by
        refine ⟨_, symRun_sound eb_hdrC (Code.e_hdrC_at (im := im)) t2 p2 (by simp [eb_hdrC.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_hdrC.res, E.eval]
        · simp only [Result.toState_getReg, eb_hdrC.res]
          t3n [g8', g9']
          unfold Keygen.nodeLo
          rw [if_neg h0, BitVec.ofNat_toNat, BitVec.setWidth_eq]
          have hl' : BitVec.ofNat 64 ((lay + 18446744073709551615) * 281474976710656) =
              BitVec.ofNat 64 ((lay - 1) * 281474976710656) := by
            apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
          rw [hl', show (513#64) = BitVec.ofNat 64 513 from rfl,
            ofNat_or_disjoint 513 (tree * 65536) 16 (by decide) (by omega),
            ofNat_or_disjoint' _ ((lay - 1) * 281474976710656) 48 (by omega) (by omega),
            show (13907115649320091648#64) = BitVec.ofNat 64 (193 * 2 ^ 56) from rfl,
            ofNat_or_disjoint' _ (193 * 2 ^ 56) 56 (by omega) (by omega)]
          unfold T3.hyperWord
          congr 1
          rw [Nat.mod_eq_of_lt htree, Nat.mod_eq_of_lt (by omega : lay - 1 < 256)]
          omega
        · simp only [Result.toState_getReg, eb_hdrC.res, rv_simp, g13]
        · ex_regs eb_hdrC.res
        · intro A _ _; simp [eb_hdrC.res, rv_simp]
      refine ⟨_, (su.trans (symRun_sound eb_hdrT (Code.e_hdrT_at (im := im)) u pu (by simp [eb_hdrT.res, rv_simp]))).of_eq
        (by simp [h0, eb_hdrT.res]) (by simp [h0, eb_hdrT.res]), ?_, ?_, ?_, ?_, ?_⟩
      · exact eb_hdrT_pc u
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_low, eb_hdrT_x6, uor, u13]
        unfold Keygen.nodeLo ClaudeWCT.WCT9.lowerK
        rw [if_neg h0, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc, ofNat_add_ofNat,
          Nat.add_comm heap 1407]
      · rw [ClaudeWCT.WCT9.merkleTweak_lower h0, ClaudeWCT.WCT9.lowerTweak_high, eb_hdrT_x7]
      · exact (ru.trans (eb_hdrT_regs u)).mono (by decide)
      · exact (fu.trans (eb_hdrT_frame u)).mono (fun A _ h => by simp_all)
  obtain ⟨t4, s4, p4, m16, m24, x10, x11, x12, r4, f4⟩ : ∃ t, Steps im t3 9 9 t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = (ClaudeWCT.WCT9.merkleTweak lay tree heap).extractLsb' 64 64 ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t3 t [.x10, .x11, .x12, .x28] ∧ Frame t3 t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
    refine ⟨_, symRun_sound eb_hdrE (Code.e_hdrE_at (im := im)) t3 p3 (by simp [eb_hdrE.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrE.res, E.eval]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y6]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y7]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · exact eb_hdrE_regs t3
    · intro A hA hn
      simp only [NODE] at hn
      simp only [Result.toState_getMem, eb_hdrE.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hdrK; split_ifs <;> simp_all)
    (by unfold hdrK; split_ifs <;> simp_all), p4, m16, m24, x10, x11, x12,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

theorem rl1139_spec (hpc : s.pc = pcOf 1139) (P M j : Nat) (hM : 64 ≤ M) (hM' : M < 2 ^ 64)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x22, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1139 (Code.codeAt_1139 (im := im)) s hpc (by simp [eblk_1139.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1139.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h22, ofNat_add_ofNat]
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h24]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, toNat_ofNat_lt hM', toNat_ofNat_lt (show M - 64 < 2 ^ 64 by omega),
      show (64#64 : Word).toNat = 64 from rfl]; omega
  · simp only [Result.toState_getReg, eblk_1139.res, rv_simp, h20, ofNat_add_ofNat]
  · ex_regs eblk_1139.res
  · intro A _ _; simp [eblk_1139.res, rv_simp]

theorem rl1143_spec (hpc : s.pc = pcOf 1143) (ret : Nat) (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps im s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_1143 (Code.codeAt_1143 (im := im)) s hpc (by simp [eblk_1143.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1143.res, rv_simp, h1, pcOf_and_max]
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · simp only [Result.toState_getMem, eblk_1143.res, ENC, NOUT]
    t3n []
  · ex_regs eblk_1143.res
  · intro A hA hn
    simp only [ENC] at hn
    simp only [Result.toState_getMem, eblk_1143.res]
    t3n []
    rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
theorem fetch_43780 (hpc : s.pc = pcOf 43780) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_43780 (im := im)).fetch s hpc).trans rfl
theorem fetch_43788 (hpc : s.pc = pcOf 43788) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_43788 (im := im)).fetch s hpc).trans rfl
theorem fetch_1072 (hpc : s.pc = pcOf 1072) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_1072 (im := im)).fetch s hpc).trans rfl
theorem fetch_1138 (hpc : s.pc = pcOf 1138) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_1138 (im := im)).fetch s hpc).trans rfl
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_packed : PackedBlocks.Code Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_bc : BCBlocks.Code Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel
theorem installed_code : Code Images.expandImage := by
  constructor <;> first
    | (apply codeAt_expand_current_chunk <;> decide +kernel)
    | (apply codeAt_expand_last <;> decide +kernel)
#print axioms installed_packed
#print axioms installed_bc
#print axioms installed_code
end SigGolfCandidate.T3M.Expand.SharedRecover
