import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075

-- ==== merged from T3M_Expand_LayerBlocks ====
section

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
def e_hpZ : List (BitVec 32) := [929827,930851,0xbb0d706f]
sym_block eb_hpZ := symRun { noAlias := true } e_hpZ (pcOf 42755) 30
def e_hpJ : List (BitVec 32) := [0xbb0d706f]
sym_block eb_hpJ := symRun { noAlias := true } e_hpJ (pcOf 42757) 30
def e_w1009 : List (BitVec 32) := [2451]
sym_block eb_w1009 := symRun { noAlias := true } e_w1009 (pcOf 1009) 30
/-- T51: 42759 (#938 `beq s0,zero,42763`, the top slot `+32` path) is a NOP: the endpad top leaf uses the lower
slots (`end_0` at `LEAFPK`, `end_i` at `LEAFPK + 16 i + 16`). -/
def e_slA : List (BitVec 32) := [4824595,0x13]
sym_block eb_slA := symRun { noAlias := true } e_slA (pcOf 42758) 30
def e_slB : List (BitVec 32) := [624739]
sym_block eb_slB := symRun { noAlias := true } e_slB (pcOf 42760) 30
def e_slN : List (BitVec 32) := [17698323,0xc48d706f]
sym_block eb_slN := symRun { noAlias := true } e_slN (pcOf 42761) 30
def e_slT : List (BitVec 32) := [34475539,0xc40d706f]
sym_block eb_slT := symRun { noAlias := true } e_slT (pcOf 42763) 30
def e_slZ : List (BitVec 32) := [0xc40d706f]
sym_block eb_slZ := symRun { noAlias := true } e_slZ (pcOf 42764) 30
/-! T51 KMAX (54532..54542, from 1158 `j 54532`): `s5` = the top chain cap `maxDigit 0 i` (5 for `i < 27`, 4 for
`i < 48`, 6 for `i < 50`, else 5), then `j 1031`. -/
def e_kmax0 : List (BitVec 32) := [0x00500a93,0x01b00e13,0x03c9c063]
sym_block eb_kmax0 := symRun { noAlias := true } e_kmax0 (pcOf 54532) 30
def e_kmax1 : List (BitVec 32) := [0x00400a93,0x03000e13,0x01c9ca63]
sym_block eb_kmax1 := symRun { noAlias := true } e_kmax1 (pcOf 54535) 30
def e_kmax2 : List (BitVec 32) := [0x00600a93,0x03200e13,0x01c9c463]
sym_block eb_kmax2 := symRun { noAlias := true } e_kmax2 (pcOf 54538) 30
def e_kmax3 : List (BitVec 32) := [0x00500a93,0xbe5cb06f]
sym_block eb_kmax3 := symRun { noAlias := true } e_kmax3 (pcOf 54541) 30
def e_kmax4 : List (BitVec 32) := [0xbe5cb06f]
sym_block eb_kmax4 := symRun { noAlias := true } e_kmax4 (pcOf 54542) 30
/-! T51 GT (54543..54552, from 49311 `j 54543`): `t1` = the G terminal step `maxDigit 0 i - 1` (4, 3 for
`27 <= i < 48`, 5 for `i = 48`) and 7 for chain 0 (it keeps the HIGH half on every step), then `j 49315`. -/
def e_gt0 : List (BitVec 32) := [0x00400313,0xfe598393,0x0153b393,0x40730333,0xfd098393,0x0013b393,0x00730333,
  0x00099463]
sym_block eb_gt0 := symRun { noAlias := true } e_gt0 (pcOf 54543) 30
def e_gt1 : List (BitVec 32) := [0x00700313,0xe2dfa06f]
sym_block eb_gt1 := symRun { noAlias := true } e_gt1 (pcOf 54551) 30
def e_gt2 : List (BitVec 32) := [0xe2dfa06f]
sym_block eb_gt2 := symRun { noAlias := true } e_gt2 (pcOf 54552) 30
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
def slotOff (_lay : T3.Layer) (c : Nat) : Nat := if c = 0 then 0 else 16 * c + 16
def hpK (lay : T3.Layer) : Nat := if lay = 0 then 19 else 17
def slK (_lay : T3.Layer) (i : Nat) : Nat := if i = 0 then 5 else 6
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
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
def seg_n1139 : List (BitVec 32) := [0x1202906f]
def seg_1140 : List (BitVec 32) := [4228647955,1706515,4020236399]
def nonce_A : List (BitVec 32) := [0xc00e13,0xdc79863]
def nonce_B : List (BitVec 32) := [0xb00e13,0xdca7463]
/-- T51: 43199 `addi a3,s4,1` (`h`), 43200 `j 54553` (ZB; #938 `mv a4,a3`, then 43201..43214 computed `b = h`). -/
def nonce_C : List (BitVec 32) := [0x1a0693,0x1640b06f]
/-! T51 ZB (54553..54568): `a4 = b_h = topZeroBits h` (0 for `h < 3`, 1 for `h = 3`, else `h - 3`) and the zero-test
mask `t6` (0 for `b_h = 0`, the top `b_h` bits, bits 40..47 for `h = 11`), then `j 43215`. -/
def nonce_Z0 : List (BitVec 32) := [0x00000713,0x00000f93,0x00300e13,0x03c6c863]
def nonce_Z1 : List (BitVec 32) := [0xffd68713,0x00071463]
def nonce_Z2 : List (BitVec 32) := [0x00100713,0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z3 : List (BitVec 32) := [0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z4 : List (BitVec 32) := [0x0ff00f93,0x028f9f93,0xe9df406f]
def nonce_Z5 : List (BitVec 32) := [0xe9df406f]
def nonce_D : List (BitVec 32) := [0x800e13,0x80006f]
def nonce_E : List (BitVec 32) := [0x4000e13,0x40ee0e33,0xfff00f93,0x1cf9fb3,0xb00e13,0x1c69663]
def nonce_F : List (BitVec 32) := [0x7ff00f93,0x22f9f93]
def nonce_G : List (BitVec 32) := [0x6800893,0xe898b3,0xd95eb3,0x1efe93,0x100f13,0x41df0eb3,0x4e9e93,0x20f37,0x240f0f13,0x1ee8eb3]
def nonce_L : List (BitVec 32) := [0x8ebf03,0x1ff7f33,0x20f0a63]
def nonce_H : List (BitVec 32) := [0x20e37,0x220e3f03,0x1f0f13,0x31f7263]
def nonce_I : List (BitVec 32) := [0x23ee3023,0x20537,0x20050513,0x4000593,0x20637,0x24060613]
def nonce_E43238 : List (BitVec 32) := [0x73]
def nonce_J : List (BitVec 32) := [0xfc9ff06f]
def nonce_K : List (BitVec 32) := [0x20e37,0x220e3f03,0x220e3023,0x66e37,0x752e3c23,0x3a1e93,0x1de0e33,0x71ee3023]
def nonce_S : List (BitVec 32) := [0x10b0b13,0xe0dd606f]
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
  e_hpJ_at : CodeAt im (pcOf 42757) e_hpJ
  e_w1009_at : CodeAt im (pcOf 1009) e_w1009
  e_slA_at : CodeAt im (pcOf 42758) e_slA
  e_slB_at : CodeAt im (pcOf 42760) e_slB
  e_slN_at : CodeAt im (pcOf 42761) e_slN
  e_slZ_at : CodeAt im (pcOf 42764) e_slZ
  codeAt_1010 : CodeAt im (pcOf 1010) seg_1010
  codeAt_1011 : CodeAt im (pcOf 1011) seg_1011
  codeAt_1027 : CodeAt im (pcOf 1027) seg_1027
  codeAt_1028 : CodeAt im (pcOf 1028) seg_1028
  codeAt_1030 : CodeAt im (pcOf 1030) seg_1030
  codeAt_1031 : CodeAt im (pcOf 1031) seg_1031
  -- Witness stack: 1041 `jal 49300` and the chain step block 49300..49337.
  codeAt_1041 : CodeAt im (pcOf 1041) seg_1041
  codeAt_49300 : CodeAt im (pcOf 49300) seg_49300
  codeAt_49301 : CodeAt im (pcOf 49301) seg_49301
  codeAt_49303 : CodeAt im (pcOf 49303) seg_49303
  codeAt_49306 : CodeAt im (pcOf 49306) seg_49306
  codeAt_49309 : CodeAt im (pcOf 49309) seg_49309
  codeAt_49311 : CodeAt im (pcOf 49311) seg_49311
  e_gt0_at : CodeAt im (pcOf 54543) e_gt0
  e_gt1_at : CodeAt im (pcOf 54551) e_gt1
  e_gt2_at : CodeAt im (pcOf 54552) e_gt2
  codeAt_49315 : CodeAt im (pcOf 49315) seg_49315
  codeAt_49316 : CodeAt im (pcOf 49316) seg_49316
  codeAt_49327 : CodeAt im (pcOf 49327) seg_49327
  codeAt_49328 : CodeAt im (pcOf 49328) seg_49328
  codeAt_49329 : CodeAt im (pcOf 49329) seg_49329
  codeAt_49331 : CodeAt im (pcOf 49331) seg_49331
  codeAt_49336 : CodeAt im (pcOf 49336) seg_49336
  codeAt_49337 : CodeAt im (pcOf 49337) seg_49337
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
  codeAt_1139 : CodeAt im (pcOf 1139) seg_n1139
  codeAt_1140 : CodeAt im (pcOf 1140) seg_1140
  codeAt_nA : CodeAt im (pcOf 43195) nonce_A
  codeAt_nB : CodeAt im (pcOf 43197) nonce_B
  codeAt_nC : CodeAt im (pcOf 43199) nonce_C
  codeAt_nZ0 : CodeAt im (pcOf 54553) nonce_Z0
  codeAt_nZ1 : CodeAt im (pcOf 54557) nonce_Z1
  codeAt_nZ2 : CodeAt im (pcOf 54559) nonce_Z2
  codeAt_nZ3 : CodeAt im (pcOf 54560) nonce_Z3
  codeAt_nZ4 : CodeAt im (pcOf 54566) nonce_Z4
  codeAt_nZ5 : CodeAt im (pcOf 54568) nonce_Z5
  codeAt_nG : CodeAt im (pcOf 43215) nonce_G
  codeAt_nL : CodeAt im (pcOf 43225) nonce_L
  codeAt_nH : CodeAt im (pcOf 43228) nonce_H
  codeAt_nI : CodeAt im (pcOf 43232) nonce_I
  codeAt_n43238 : CodeAt im (pcOf 43238) nonce_E43238
  codeAt_nJ : CodeAt im (pcOf 43239) nonce_J
  codeAt_nK : CodeAt im (pcOf 43240) nonce_K
  codeAt_nS : CodeAt im (pcOf 43248) nonce_S
  codeAt_1143 : CodeAt im (pcOf 1143) seg_1143
  codeAt_1158 : CodeAt im (pcOf 1158) seg_1158
  e_kmax0_at : CodeAt im (pcOf 54532) e_kmax0
  e_kmax1_at : CodeAt im (pcOf 54535) e_kmax1
  e_kmax2_at : CodeAt im (pcOf 54538) e_kmax2
  e_kmax3_at : CodeAt im (pcOf 54541) e_kmax3
  e_kmax4_at : CodeAt im (pcOf 54542) e_kmax4
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
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
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
  obtain ⟨t3, s3, p3, z0, r3, f3⟩ : ∃ t, Steps im t2 (if lay = 0 then 3 else 1) (if lay = 0 then 3 else 1) t ∧
      t.pc = pcOf 1009 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept t2 t [] ∧ Frame t2 t (fun A => A = LEAFPK ∨ A = LEAFPK + 8) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      refine ⟨_, (symRun_sound eb_hpZ (Code.e_hpZ_at (im := im)) t2 p2
        (by simp [eb_hpZ.res, rv_simp, x28, accessValid_iff, MEMORY_BYTES, LEAFPK])).of_eq (by simp [h0, eb_hpZ.res])
        (by simp [h0, eb_hpZ.res]),
        ?_, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpZ.res, E.eval]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28, LEAFPK]
      · intro r hr; cases r <;> rfl
      · intro A hA hn
        simp only [Result.toState_getMem, eb_hpZ.res]
        t3n [x28]
        simp only [LEAFPK] at hn ⊢
        rw [if_neg (by omega), if_neg (by omega)]
    · rw [if_neg h0] at p2
      refine ⟨_, (symRun_sound eb_hpJ (Code.e_hpJ_at (im := im)) t2 p2 (by simp [eb_hpJ.res, rv_simp])).of_eq (by simp [h0, eb_hpJ.res])
        (by simp [h0, eb_hpJ.res]), ?_, fun h => absurd h h0, ?_, ?_⟩
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
    (by unfold hpK; split_ifs <;> simp_all), p4, x19, ?_, ?_, fun h => ?_,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h <;> simp only [LEAFPK] at h ⊢ <;> omega)⟩
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m16]
  · rw [f4.get (by simp only [LEAFPK]; omega) (by simp), f3.get (by simp only [LEAFPK]; omega)
      (by simp only [LEAFPK]; omega), m24]
  · obtain ⟨a, b⟩ := z0 h
    exact ⟨by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), a],
      by rw [f4.get (by simp only [LEAFPK]; omega) (by simp), b]⟩

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

/-- T51 KMAX steps from 1158 to 1031 (1158 `j 54532`, the cap ladder, `j 1031`). -/
def kmaxSteps (i : Nat) : Nat := if i < 27 then 5 else if i < 48 then 8 else if i < 50 then 11 else 12
theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (kmaxSteps i) (kmaxSteps i) t ∧ t.pc = pcOf 1031 ∧
      t.getReg .x21 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i) ∧ RegsExcept s t [.x21, .x28] ∧
      Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54532 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1158 (Code.codeAt_1158 (im := im)) s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1158.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  have j4 : ∀ u : MachineState, u.pc = pcOf 54542 → ∃ v, Steps im u 1 1 v ∧ v.pc = pcOf 1031 ∧
      RegsExcept u v [] ∧ Frame u v (fun _ => False) := fun u hu => by
    refine ⟨_, symRun_sound eb_kmax4 (Code.e_kmax4_at (im := im)) u hu (by simp [eb_kmax4.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax4.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have hmd : SigGolfCandidate.T3.maxDigit 0 i =
      (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) := by
    simp [SigGolfCandidate.T3.maxDigit]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 3 3 t ∧
      t.pc = (if i < 27 then pcOf 54542 else pcOf 54535) ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t0 t [.x21, .x28] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax0 (Code.e_kmax0_at (im := im)) t0 p0 (by simp [eb_kmax0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax0.res, E.eval, CmpOp.eval, RegFile.get, g19]
      rw [show (27#64 : Word) = BitVec.ofNat 64 27 from rfl, ex_slt i 27 hi (by norm_num)]
      by_cases hi' : i < 27 <;> simp [hi']
    · simp [eb_kmax0.res, rv_simp]
    · ex_regs eb_kmax0.res
    · intro A _ _; simp [eb_kmax0.res, rv_simp]
  by_cases h27 : i < 27
  · rw [if_pos h27] at p1
    obtain ⟨t2, s2, p2, r2, f2⟩ := j4 t1 p1
    refine ⟨t2, ((s0.trans s1).trans s2).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p2, by rw [r2.get (by decide), x1, hmd, if_pos h27],
      ((r0.trans r1).trans r2).mono (by decide), ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h27] at p1
  have g19a : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), g19]
  obtain ⟨t2, s2, p2, x2, r2, f2⟩ : ∃ t, Steps im t1 3 3 t ∧
      t.pc = (if i < 48 then pcOf 54542 else pcOf 54538) ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept t1 t [.x21, .x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax1 (Code.e_kmax1_at (im := im)) t1 p1 (by simp [eb_kmax1.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax1.res, E.eval, CmpOp.eval, RegFile.get, g19a]
      rw [show (48#64 : Word) = BitVec.ofNat 64 48 from rfl, ex_slt i 48 hi (by norm_num)]
      by_cases hi' : i < 48 <;> simp [hi']
    · simp [eb_kmax1.res, rv_simp]
    · ex_regs eb_kmax1.res
    · intro A _ _; simp [eb_kmax1.res, rv_simp]
  by_cases h48 : i < 48
  · rw [if_pos h48] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := j4 t2 p2
    refine ⟨t3, (((s0.trans s1).trans s2).trans s3).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p3, by rw [r3.get (by decide), x2, hmd, if_neg h27, if_pos h48],
      (((r0.trans r1).trans r2).trans r3).mono (by decide),
      (((f0.trans f1).trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h48] at p2
  have g19b : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19a]
  obtain ⟨t3, s3, p3, x3, r3, f3⟩ : ∃ t, Steps im t2 3 3 t ∧
      t.pc = (if i < 50 then pcOf 54542 else pcOf 54541) ∧ t.getReg .x21 = BitVec.ofNat 64 6 ∧
      RegsExcept t2 t [.x21, .x28] ∧ Frame t2 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax2 (Code.e_kmax2_at (im := im)) t2 p2 (by simp [eb_kmax2.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_kmax2.res, E.eval, CmpOp.eval, RegFile.get, g19b]
      rw [show (50#64 : Word) = BitVec.ofNat 64 50 from rfl, ex_slt i 50 hi (by norm_num)]
      by_cases hi' : i < 50 <;> simp [hi']
    · simp [eb_kmax2.res, rv_simp]
    · ex_regs eb_kmax2.res
    · intro A _ _; simp [eb_kmax2.res, rv_simp]
  by_cases h50 : i < 50
  · rw [if_pos h50] at p3
    obtain ⟨t4, s4, p4, r4, f4⟩ := j4 t3 p3
    refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
      (by unfold kmaxSteps; split_ifs <;> omega), p4,
      by rw [r4.get (by decide), x3, hmd, if_neg h27, if_neg h48, if_pos h50],
      ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
      ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
  rw [if_neg h50] at p3
  obtain ⟨t4, s4, p4, x4, r4, f4⟩ : ∃ t, Steps im t3 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 5 ∧
      RegsExcept t3 t [.x21] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_kmax3 (Code.e_kmax3_at (im := im)) t3 p3 (by simp [eb_kmax3.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_kmax3.res, E.eval]
    · simp [eb_kmax3.res, rv_simp]
    · ex_regs eb_kmax3.res
    · intro A _ _; simp [eb_kmax3.res, rv_simp]
  refine ⟨t4, ((((s0.trans s1).trans s2).trans s3).trans s4).of_eq (by unfold kmaxSteps; split_ifs <;> omega)
    (by unfold kmaxSteps; split_ifs <;> omega), p4,
    by rw [x4, hmd, if_neg h27, if_neg h48, if_neg h50],
    ((((r0.trans r1).trans r2).trans r3).trans r4).mono (by decide),
    ((((f0.trans f1).trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩

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

/-- The F path's C3 tail `jal 43451` (at 49337) and its trampoline (an F chain: `isG = false`). -/
theorem rl1047_spec (hpc : s.pc = pcOf 49337) (lay : T3.Layer) (i m : Nat) (hi : i < 2 ^ 64) (hm : m < 2 ^ 63)
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
    refine ⟨_, symRun_sound eblk_49337 (Code.codeAt_49337 (im := im)) s hpc (by simp [eblk_49337.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_49337.res, E.eval]
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
    have hs : ClaudeWCT.WCT9.chainHigh lay i m = false := by
      exfalso
      have hl : lay = 0 := Fin.ext hl0
      subst hl hi0'
      simp [ClaudeWCT.WCT9.isG, SigGolfCandidate.T3.topIsG] at hG
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
    ClaudeWCT.WCT9.chainHigh_eq_true.mpr (Or.inl ⟨fun h => hl0 (by rw [h]; rfl), Or.inl ⟨hi0', hm6'⟩⟩)
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

/-! ### Witness stack: the chain step block 49300..49337 (lower G, top G with the top rule, F) -/
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

/-- 1041 `jal 49300`, 49300 `beq s0,zero,49306`. -/
theorem sel_spec (hpc : s.pc = pcOf 1041) (lay : Nat) (hlay : lay < 2 ^ 64)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 49306 else pcOf 49301) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 49300 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1041 (Code.codeAt_1041 (im := im)) s hpc (by simp [eblk_1041.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [eblk_1041.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  refine ⟨_, s0.trans (symRun_sound eblk_49300 (Code.codeAt_49300 (im := im)) t0 p0
    (by simp [eblk_49300.res, rv_simp])), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49300.res, E.eval, CmpOp.eval, r0.get (by simp), h8]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq hlay (by norm_num)]
    by_cases h0 : lay = 0 <;> simp [h0]
  · have r1 : RegsExcept t0 (eblk_49300.res.toState t0) [] := by
      intro r hr; cases r <;> rfl
    exact (r0.trans r1).mono (by simp)
  · have f1 : Frame t0 (eblk_49300.res.toState t0) (fun _ => False) := by
      intro A _ _; rfl
    exact (f0.trans f1).mono (fun A _ h => by simp_all)

/-- Lower layer: 49301 `andi t1,s3,1`, 49302 `beq t1,zero,49331`. -/
theorem lsel_spec (hpc : s.pc = pcOf 49301) (i : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if i % 2 = 0 then pcOf 49331 else pcOf 49303) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49301 (Code.codeAt_49301 (im := im)) s hpc (by simp [eblk_49301.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49301.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_eq (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49301.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49301.res, rv_simp]

/-- Lower G: 49303 `addi t1,zero,6`, 49304 `addi t2,zero,0`, 49305 `jal 49316`. -/
theorem lg_spec (hpc : s.pc = pcOf 49303) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = pcOf 49316 ∧ t.getReg .x6 = BitVec.ofNat 64 6 ∧
      t.getReg .x7 = BitVec.ofNat 64 0 ∧ RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49303 (Code.codeAt_49303 (im := im)) s hpc (by simp [eblk_49303.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49303.res, E.eval]
  · simp [eblk_49303.res, rv_simp]
  · simp [eblk_49303.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49303.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49303.res, rv_simp]

/-- Top: 49306 `andi t1,s3,1`, 49307 `addi t2,zero,0`, 49308 `bne t1,t2,49331`. -/
theorem tsel_spec (hpc : s.pc = pcOf 49306) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 3 3 t ∧ t.pc = (if i % 2 = 0 then pcOf 49309 else pcOf 49331) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49306 (Code.codeAt_49306 (im := im)) s hpc (by simp [eblk_49306.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49306.res, E.eval, CmpOp.eval, BinOp.eval, rv_simp, h19, pe_and1]
    rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
    by_cases h0 : i % 2 = 0 <;> simp [h0]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49306.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49306.res, rv_simp]

/-- Top: 49309 `addi t2,zero,52`, 49310 `blt t2,s3,49331`. -/
theorem tle_spec (hpc : s.pc = pcOf 49309) (i : Nat) (hi : i < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if 52 < i then pcOf 49331 else pcOf 49311) ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49309 (Code.codeAt_49309 (im := im)) s hpc (by simp [eblk_49309.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_49309.res, E.eval, CmpOp.eval, rv_simp, h19]
    rw [show (BitVec.ofNat 64 52 : Word) = BitVec.ofNat 64 52 from rfl, ofNat_slt 52 i (by norm_num) hi]
    by_cases h : 52 < i <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49309.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49309.res, rv_simp]

/-- T51 top G: 49311 `j 54543`, GT 54543..54552 (`t1 := 4 - [27 <= i < 48] + [i = 48]`, 7 for chain 0), 49315
`ld t2,24(t3)`: the step at which the G chain writes LOW (`gTerm`: `maxDigit 0 i - 1`; chain 0 never) and the header
high word. -/
def gTerm (i : Nat) : Nat := if i = 0 then 7 else SigGolfCandidate.T3.maxDigit 0 i - 1
def gtK (i : Nat) : Nat := if i = 0 then 12 else 11
theorem tcap_spec (hpc : s.pc = pcOf 49311) (i : Nat) (hi : i ≤ 52) (hev : i % 2 = 0)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (gtK i) (gtK i) t ∧ t.pc = pcOf 49316 ∧
      t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      t.getReg .x7 = s.getMem (BitVec.ofNat 64 (CHAIN + 24)) ∧
      RegsExcept s t [.x6, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t0, s0, p0, r0, f0⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 54543 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_49311 (Code.codeAt_49311 (im := im)) s hpc (by simp [eblk_49311.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_49311.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A _ _; rfl
  have g19 : t0.getReg .x19 = BitVec.ofNat 64 i := by rw [r0.get (by decide), h19]
  obtain ⟨t1, s1, p1, x1, r1, f1⟩ : ∃ t, Steps im t0 8 8 t ∧
      t.pc = (if i = 0 then pcOf 54551 else pcOf 54552) ∧
      t.getReg .x6 = BitVec.ofNat 64 (SigGolfCandidate.T3.maxDigit 0 i - 1) ∧
      RegsExcept t0 t [.x6, .x7] ∧ Frame t0 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_gt0 (Code.e_gt0_at (im := im)) t0 p0 (by simp [eb_gt0.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_gt0.res, E.eval, CmpOp.eval, g19]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, pe_ne (by omega) (by norm_num)]
      by_cases h0 : i = 0 <;> simp [h0]
    · simp only [Result.toState_getReg, eb_gt0.res, rv_simp, g19]
      interval_cases i <;> first | decide | (exfalso; omega)
    · ex_regs eb_gt0.res
    · intro A _ _; simp [eb_gt0.res, rv_simp]
  obtain ⟨t2, k2, s2, hk2, p2, x2, r2, f2⟩ : ∃ t k, Steps im t1 k k t ∧ k = (if i = 0 then 2 else 1) ∧
      t.pc = pcOf 49315 ∧ t.getReg .x6 = BitVec.ofNat 64 (gTerm i) ∧
      RegsExcept t1 t [.x6] ∧ Frame t1 t (fun _ => False) := by
    by_cases h0 : i = 0
    · rw [if_pos h0] at p1
      refine ⟨_, 2, symRun_sound eb_gt1 (Code.e_gt1_at (im := im)) t1 p1 (by simp [eb_gt1.res, rv_simp]),
        by rw [if_pos h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt1.res, E.eval]
      · simp [eb_gt1.res, rv_simp, gTerm, h0]
      · ex_regs eb_gt1.res
      · intro A _ _; simp [eb_gt1.res, rv_simp]
    · rw [if_neg h0] at p1
      refine ⟨_, 1, symRun_sound eb_gt2 (Code.e_gt2_at (im := im)) t1 p1 (by simp [eb_gt2.res, rv_simp]),
        by rw [if_neg h0], ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_gt2.res, E.eval]
      · simp only [Result.toState_getReg, eb_gt2.res, rv_simp, x1, gTerm, if_neg h0]
      · intro r hr; cases r <;> rfl
      · intro A _ _; rfl
  have r02 : RegsExcept s t2 [.x6, .x7] := ((r0.trans r1).trans r2).mono (by decide)
  have v28 : t2.getReg .x28 = BitVec.ofNat 64 CHAIN := by rw [r02.get (by simp)]; exact h28
  have hobl : Oblig.all t2 eblk_49315.res.st.obl := by
    simp only [eblk_49315.res]
    t3n [v28, CHAIN]
    try norm_num
  have sw := symRun_sound eblk_49315 (Code.codeAt_49315 (im := im)) t2 p2 hobl
  have f02 : Frame s t2 (fun _ => False) := ((f0.trans f1).trans f2).mono (fun A _ h => by simp_all)
  refine ⟨_, (((s0.trans s1).trans s2).trans sw).of_eq (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res])
    (by unfold gtK; rw [hk2]; split_ifs <;> simp [eblk_49315.res]), by simp [eblk_49315.res, E.eval], ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_getReg, eblk_49315.res, rv_simp]; exact x2
  · rw [← f02.get (A := CHAIN + 24) (by decide) (by simp)]
    simp only [Result.toState_getReg, eblk_49315.res, rv_simp]
    t3n [v28, CHAIN]
  · have rw' : RegsExcept t2 (eblk_49315.res.toState t2) [.x7] := by
      intro r hr; simp at hr; cases r <;> simp_all [eblk_49315.res, rv_simp] <;> rfl
    exact (r02.trans rw').mono (by simp)
  · intro A hA _
    rw [show (eblk_49315.res.toState t2).getMem (BitVec.ofNat 64 A) = t2.getMem (BitVec.ofNat 64 A) by
      simp [eblk_49315.res, rv_simp]]
    exact (f02.get hA (by simp))

/-- The G body 49316..49326 (and 49327 on the terminal step `m = T`): `CHAIN+64 := CHAIN+16`, `CHAIN+72 := t2`,
pads, HASH arguments. -/
theorem g_spec (hpc : s.pc = pcOf 49316) (m T : Nat) (Y : Word)
    (hm : m < 2 ^ 63) (hT : T < 2 ^ 63) (h6 : s.getReg .x6 = BitVec.ofNat 64 T) (h7 : s.getReg .x7 = Y)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 m) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s (11 + (if m = T then 1 else 0)) (11 + (if m = T then 1 else 0)) t ∧ t.pc = pcOf 49328 ∧
      t.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (if m = T then CHAIN + 48 else CHAIN + 32) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12, .x30] ∧ Frame s t (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
  have hobl : Oblig.all s eblk_49316.res.st.obl := by
    simp only [eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  have st := symRun_sound eblk_49316 (Code.codeAt_49316 (im := im)) s hpc hobl
  set u := eblk_49316.res.toState s with hu
  have upc : u.pc = (if m = T then pcOf 49327 else pcOf 49328) := by
    simp only [hu, Result.toState_pc, eblk_49316.res, E.eval, CmpOp.eval, h20, h6]
    rw [pe_ne (by omega) (by omega)]
    by_cases hm6 : m = T <;> simp [hm6]
  have ur : RegsExcept s u [.x10, .x11, .x12, .x30] := by
    intro r hr; simp at hr; cases r <;> simp_all [hu, eblk_49316.res, rv_simp] <;> rfl
  have uf : Frame s u (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) := by
    intro A hA hn
    simp only [hu, Result.toState_getMem, eblk_49316.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131560 by omega, show ¬ A = 131568 by omega, show ¬ A = 131576 by omega,
      show ¬ A = 131584 by omega, show ¬ A = 131592 by omega, show ¬ A = 131552 by omega, if_false]
  have u10 : u.getReg .x10 = BitVec.ofNat 64 (CHAIN + 48) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have u11 : u.getReg .x11 = BitVec.ofNat 64 64 := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp] <;> rfl
  have u12 : u.getReg .x12 = BitVec.ofNat 64 (CHAIN + 32) := by
    simp only [hu, Result.toState_getReg, eblk_49316.res, rv_simp, h28] <;> rfl
  have umem : u.getMem (BitVec.ofNat 64 (CHAIN + 64)) = s.getMem (BitVec.ofNat 64 (CHAIN + 16)) ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 72)) = Y ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 80)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 88)) = 0 ∧ u.getMem (BitVec.ofNat 64 (CHAIN + 96)) = 0 ∧
      u.getMem (BitVec.ofNat 64 (CHAIN + 104)) = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · simp only [hu, Result.toState_getMem, eblk_49316.res]
      t3n [h28, h7, CHAIN, Nat.reduceLeDiff, and_true]
  by_cases hm6 : m = T
  · rw [if_pos hm6] at upc
    have hobl6 : Oblig.all u eblk_49327.res.st.obl := by simp [eblk_49327.res, rv_simp]
    have st6 := symRun_sound eblk_49327 (Code.codeAt_49327 (im := im)) u upc hobl6
    refine ⟨_, (st.trans st6).of_eq (by simp [hm6, eblk_49316.res, eblk_49327.res])
      (by simp [hm6, eblk_49316.res, eblk_49327.res]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [eblk_49327.res, E.eval]
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u10
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp]; exact u11
    · simp only [Result.toState_getReg, eblk_49327.res, rv_simp, if_pos hm6, ur.get (show Reg.x28 ∉ _ by simp), h28]
      rfl
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.1
    · simp only [Result.toState_getMem, eblk_49327.res, rv_simp]; exact umem.2.2.2.2.2
    · intro r hr
      rw [show (eblk_49327.res.toState u).getReg r = u.getReg r by
        cases r <;> simp_all [eblk_49327.res, rv_simp] <;> rfl]
      exact ur r hr
    · intro A hA hn
      rw [show (eblk_49327.res.toState u).getMem (BitVec.ofNat 64 A) = u.getMem (BitVec.ofNat 64 A) by
        simp [eblk_49327.res, rv_simp]]
      exact uf A hA hn
  · rw [if_neg hm6] at upc
    refine ⟨u, st.of_eq (by simp [hm6, eblk_49316.res]) (by simp [hm6, eblk_49316.res]), upc, u10, u11, ?_, umem.1,
      umem.2.1, umem.2.2.1, umem.2.2.2.1, umem.2.2.2.2.1, umem.2.2.2.2.2, ur, uf⟩
    rw [if_neg hm6]; exact u12

/-- The F body 49331..49335: zero the pad `CHAIN+32 .. CHAIN+48`, HASH arguments. -/
theorem f_spec (hpc : s.pc = pcOf 49331) (h28 : s.getReg .x28 = BitVec.ofNat 64 CHAIN) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = pcOf 49336 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 32)) = 0 ∧ t.getMem (BitVec.ofNat 64 (CHAIN + 40)) = 0 ∧
      RegsExcept s t [.x10, .x11, .x12] ∧ Frame s t (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) := by
  have hobl : Oblig.all s eblk_49331.res.st.obl := by
    simp only [eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  refine ⟨_, symRun_sound eblk_49331 (Code.codeAt_49331 (im := im)) s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [eblk_49331.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp] <;> rfl
  · simp only [Result.toState_getReg, eblk_49331.res, rv_simp, h28] <;> rfl
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · simp only [Result.toState_getMem, eblk_49331.res]; t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49331.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_49331.res]
    t3n [h28, CHAIN, Nat.reduceLeDiff, and_true]
    have hA' : A % 18446744073709551616 = A := Nat.mod_eq_of_lt hA
    simp only [CHAIN] at hn
    rw [hA']
    simp only [show ¬ A = 131520 by omega, show ¬ A = 131528 by omega, if_false]

/-- 49329 `addi s4,s4,1`, 49330 `jal 1031`. -/
theorem gtail_spec (hpc : s.pc = pcOf 49329) (m : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 m) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (m + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_49329 (Code.codeAt_49329 (im := im)) s hpc (by simp [eblk_49329.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [eblk_49329.res, E.eval]
  · simp only [Result.toState_getReg, eblk_49329.res, rv_simp, h20]
    rw [ofNat_add_ofNat]
  · intro r hr; simp at hr; cases r <;> simp_all [eblk_49329.res, rv_simp] <;> rfl
  · intro A _ _; simp [eblk_49329.res, rv_simp]

theorem rl1049_spec (hpc : s.pc = pcOf 1049) (lay : T3.Layer) (i : Nat) (hi : i < 2 ^ 59)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps im s (slK lay i) (slK lay i) t ∧ t.pc = pcOf 1052 ∧
      t.getReg .x28 = BitVec.ofNat 64 (slotOff lay i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 42758 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1049 (Code.codeAt_1049 (im := im)) s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1049.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g19 : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), h19]
  obtain ⟨t2, s2, p2, x28, r2, f2⟩ : ∃ t, Steps im t1 2 2 t ∧
      t.pc = pcOf 42760 ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧
      RegsExcept t1 t [.x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slA (Code.e_slA_at (im := im)) t1 p1 (by simp [eb_slA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_slA.res, E.eval]
    · simp only [Result.toState_getReg, eb_slA.res, rv_simp, g19]
      t3n []; congr 1; ring
    · ex_regs eb_slA.res
    · intro A _ _; simp [eb_slA.res, rv_simp]
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
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [r4.get (by decide), r3.get (by decide), x28, slotOff, if_pos hi0, hi0],
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
    refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, hi0]) (by simp [slK, hi0]), p4,
      by rw [z28, slotOff, if_neg hi0], (((r1.trans r2).trans r3).trans r4).mono (by decide),
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
theorem fetch_49328 (hpc : s.pc = pcOf 49328) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_49328 (im := im)).fetch s hpc).trans rfl
theorem fetch_49336 (hpc : s.pc = pcOf 49336) : fetch im s = some (.base .ECALL) :=
  ((Code.codeAt_49336 (im := im)).fetch s hpc).trans rfl
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
    | (apply codeAt_t51_at <;> decide)
    | (apply codeAt_expand_last <;> decide +kernel)

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
theorem finRange_map_val (n : Nat) : (List.finRange n).map Fin.val = List.range' 0 n := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp
section tb
variable {image : Image} {sk : BitVec 256}
theorem tb_shortHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a : BitVec 256, TBSim image sk (writeHash s a) W (f (a.extractLsb' 0 128)) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.shortHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_shortHash, map_eq_bind_pure_comp, bind_assoc]
  refine Sim.query_bind hf ht0 hv hq (fun a => ?_)
  have := h a
  unfold TBSim at this
  simpa only [Function.comp, pure_bind] using this
theorem tb_mapM_idx {γ δ : Type} (f : γ → T3.M δ) (idx : γ → Nat) (W : Nat) (Inv : List δ → MachineState → Prop) :
    ∀ (xs : List γ) (pre : List δ) {s : MachineState}, xs.map idx = List.range' pre.length xs.length →
    (∀ x ∈ xs, ∀ (pre' : List δ) t, pre'.length = idx x → Inv pre' t →
      TBSim image sk t W (f x) (fun d u => Inv (pre' ++ [d]) u)) →
    Inv pre s → TBSim image sk s (xs.length * W) (xs.mapM f) (fun ds u => ds.length = xs.length ∧ Inv (pre ++ ds) u)
  | [], pre, s, _, _, h0 => by
    simpa using TBSim.pure (image := image) (sk := sk) (Q := fun ds u => ds.length = 0 ∧ Inv (pre ++ ds) u)
      (a := []) (by simpa using h0)
  | x :: xs, pre, s, hidx, hb, h0 => by
    rw [List.mapM_cons]
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    have h1 := hb x (by simp) pre s hidx.1.symm h0
    have key : ∀ d t, Inv (pre ++ [d]) t → TBSim image sk t (xs.length * W)
        (do let ds ← xs.mapM f; Pure.pure (d :: ds)) (fun ds u => ds.length = xs.length + 1 ∧ Inv (pre ++ ds) u) := by
      intro d t ht
      have h2 := tb_mapM_idx f idx W Inv xs (pre ++ [d]) (by simpa using hidx.2) (fun y hy => hb y (by simp [hy])) ht
      exact (TBSim.bind (W₂ := 0) h2 (f := fun ds => Pure.pure (d :: ds))
        (fun ds u hu => TBSim.pure ⟨by simp [hu.1], by simpa using hu.2⟩)).mono (by omega) (fun _ _ h => h)
    exact (TBSim.bind h1 key).mono (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => h)
theorem tb_mapM_finRange {δ : Type} (n : Nat) (f : Fin n → T3.M δ) (W : Nat) (Inv : List δ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) (pre : List δ) t, pre.length = i.val → Inv pre t →
      TBSim image sk t W (f i) (fun d u => Inv (pre ++ [d]) u)) {s : MachineState} (h0 : Inv [] s) :
    TBSim image sk s (n * W) ((List.finRange n).mapM f) (fun ds u => ds.length = n ∧ Inv ds u) := by
  have := tb_mapM_idx f Fin.val W Inv (List.finRange n) [] (by rw [finRange_map_val]; simp)
    (fun x _ pre' t h1 h2 => hbody x pre' t h1 h2) h0
  simpa using this
theorem tb_foldlM_finRange {γ : Type} (n : Nat) (f : γ → Fin n → T3.M γ) (init : γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    TBSim image sk s (n * W) ((List.finRange n).foldlM f init) (Inv n) := by
  have gen : ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
    intro xs
    induction xs with
    | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
    | cons x xs ih =>
      intro k acc t hidx ht
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
      rw [List.foldlM_cons]
      have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
      rw [hidx.1] at h1
      refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
        (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
        simpa [Nat.add_assoc, Nat.add_comm 1] using h)
      have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
      rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
  have := gen (List.finRange n) 0 init s (by rw [finRange_map_val]; simp) h0
  simpa using this
theorem tb_foldlM_vals {γ : Type} {n : Nat} (f : γ → Fin n → T3.M γ) (W : Nat)
    (Inv : Nat → γ → MachineState → Prop)
    (hbody : ∀ (i : Fin n) acc t, Inv i.val acc t → TBSim image sk t W (f acc i) (Inv (i.val + 1))) :
    ∀ (xs : List (Fin n)) (k : Nat) (acc : γ) (t : MachineState), xs.map Fin.val = List.range' k xs.length →
      Inv k acc t → TBSim image sk t (xs.length * W) (xs.foldlM f acc) (Inv (k + xs.length)) := by
  intro xs
  induction xs with
  | nil => intro k acc t _ ht; simpa using TBSim.pure (image := image) (sk := sk) ht
  | cons x xs ih =>
    intro k acc t hidx ht
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hidx
    rw [List.foldlM_cons]
    have h1 := hbody x acc t (by rw [hidx.1]; exact ht)
    rw [hidx.1] at h1
    refine (TBSim.bind (W₂ := xs.length * W) h1 (fun acc' t' ht' => ?_)).mono
      (by rw [List.length_cons, Nat.succ_mul]; omega) (fun _ _ h => by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h)
    have := ih (k + 1) acc' t' (by simpa using hidx.2) ht'
    rwa [show k + 1 + xs.length = k + (xs.length + 1) by omega] at this
end tb
end SigGolfCandidate.T3M.Expand
end
-- ==== merged from T3M_Expand_LayerChain ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3 (Layer Digest chain chainInput shortHash pad64 zero16 header)
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS)
set_option autoImplicit false
theorem chainInput_length' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (chainInput lay tree leaf i step v).length = 64 := by
  simp [chainInput, bytesLE_length, T3.zero16]
theorem wordsOf_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    wordsOf (pad64 (chainInput lay tree leaf i step v)) =
      [0, 0, (T3.chainHeader lay tree leaf i step).extractLsb' 0 64,
        (T3.chainHeader lay tree leaf i step).extractLsb' 64 64,
        0, 0, v.extractLsb' 0 64, v.extractLsb' 64 64] := by
  rw [pad64_of_aligned _ (by rw [chainInput_length'])]
  exact Keygen.Packed.wordsOf_chainInput lay tree leaf i step v
theorem blocks_chainInput' (lay : Layer) (tree leaf i step : Nat) (v : Digest) :
    (toQ (pad64 (chainInput lay tree leaf i step v))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [chainInput_length']), blocks_toQ ⟨by rw [chainInput_length']; omega,
    by rw [chainInput_length']⟩, chainInput_length']
structure ChainCtx (lay tree leaf i : Nat) (t : MachineState) : Prop where
  x5 : t.getReg .x5 = 0
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x9 : t.getReg .x9 = BitVec.ofNat 64 tree
  x18 : t.getReg .x18 = BitVec.ofNat 64 leaf
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  z0 : t.getMem (BitVec.ofNat 64 CHAIN) = 0
  z8 : t.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0
def stepRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x20, .x28, .x30]
/-- Pairing stage 1: a chain step writes the header words and `CHAIN+32 .. CHAIN+112` (G: pads, header copy and the
interior output at `CHAIN+32`; F: the pad `CHAIN+32/40`, the output at `CHAIN+48`). -/
def StepW (A : Nat) : Prop := (A = CHAIN + 16 ∨ A = CHAIN + 24) ∨ (CHAIN + 32 ≤ A ∧ A < CHAIN + 112)
theorem ChainCtx.frame {lay tree leaf i : Nat} {t u : MachineState} (h : ChainCtx lay tree leaf i t)
    {l : List Reg} (hl : Reg.x5 ∉ l ∧ Reg.x8 ∉ l ∧ Reg.x9 ∉ l ∧ Reg.x18 ∉ l ∧ Reg.x19 ∉ l) (hr : RegsExcept t u l) (hf : Frame t u StepW) :
    ChainCtx lay tree leaf i u where
  x5 := by rw [hr.get hl.1]; exact h.x5
  x8 := by rw [hr.get hl.2.1]; exact h.x8
  x9 := by rw [hr.get hl.2.2.1]; exact h.x9
  x18 := by rw [hr.get hl.2.2.2.1]; exact h.x18
  x19 := by rw [hr.get hl.2.2.2.2]; exact h.x19
  z0 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z0
  z8 := by rw [hf.get (by simp only [CHAIN]; omega) (by unfold StepW; simp only [CHAIN]; omega)]; exact h.z8
theorem not_mem_of_sub {r : Reg} {l l' : List Reg} (hl : ∀ x ∈ l, x ∈ l') (hr : r ∉ l') : r ∉ l :=
  fun hm => hr (hl r hm)
section chain
variable {sk : BitVec 256}
def oneRegs : List Reg := [.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30]
def OneW (lay : T3.Layer) (i W : Nat) (A : Nat) : Prop :=
  StepW A ∨ A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8 ∨ A = W + 48 ∨ A = W + 56
/-- T51: the top chain caps of KMAX (`maxDigit 0 i`; `n4` is unused), lower layers 7. -/
def endpoint (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then (if i < 27 then 5 else if i < 48 then 4 else if i < 50 then 6 else 5) else 7
/-- Extra cycles of the cap selection on the top (1030 `j 1158`, KMAX). -/
def endpointExtra (lay : Layer) (i _n4 : Nat) : Nat :=
  if lay = 0 then 1 + SharedRecover.kmaxSteps i else 0
/-- Cycle budget of one chain step: the T51 top G step runs GT (+7 cycles). -/
def stepW (lay : Layer) : Nat := if lay = 0 then 67 else 60
def ChW (lay : T3.Layer) (WC k : Nat) (A : Nat) : Prop :=
  StepW A ∨ (∃ c < k, A = LEAFPK + slotOff lay c ∨ A = LEAFPK + slotOff lay c + 8) ∨
    (∃ c < k, A = WC - 64 * c + 48 ∨ A = WC - 64 * c + 56)
theorem not_ChW_of {lay : T3.Layer} {WC k A : Nat} (hk : k ≤ 58) (h1 : WC + 64 ≤ A) (h2 : A < CHAIN + 16 ∨ CHAIN + 112 ≤ A)
    (h3 : A < LEAFPK ∨ LEAFPK + 16 * 60 ≤ A) : ¬ ChW lay WC k A := by
  unfold ChW StepW
  rintro (h | ⟨c, hc, h | h⟩ | ⟨c, _, h | h⟩) <;> simp only [CHAIN, LEAFPK] at h h2 h3 <;>
    first | omega | (unfold slotOff at h; split_ifs at h <;> omega)
theorem not_ChW_hdr {lay : T3.Layer} {WC k A : Nat} (hW : WC + 64 ≤ LEAFPK) (h : A = LEAFPK + 16 ∨ A = LEAFPK + 24)
    (hk : k ≤ 54) : ¬ ChW lay WC k A := by
  rcases h with h | h
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
  · unfold ChW StepW
    rintro (h' | ⟨c, hc, h' | h'⟩ | ⟨c, _, h' | h'⟩) <;> simp only [CHAIN, LEAFPK] at h h' hW <;>
      first | omega | (unfold slotOff at h'; split_ifs at h' <;> omega)
structure ChainsInv (t0 : MachineState) (lay : Layer) (tree leaf P WC n n4 : Nat) (vals : Nat → Digest)
    (ends : List Digest) (t : MachineState) : Prop where
  pc : t.pc = pcOf 1010
  ctx : ChainCtx lay.val tree leaf ends.length t
  x23 : t.getReg .x23 = BitVec.ofNat 64 (WC - 64 * ends.length)
  slots : ∀ j < ends.length, DigAt t (LEAFPK + slotOff lay j) (ends.getD j 0)
  wvals : ∀ j < ends.length, DigAt t (WC - 64 * j + 48) (vals j)
  regs : RegsExcept t0 t oneRegs
  frame : Frame t0 t (ChW lay WC ends.length)
end chain
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3
open SigGolfCandidate.T3M.Expand
open SphincsSecurity (bytesLE bytesLE_length)
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
open ClaudeWCT
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {im : Image} [Code im] [BCBlocks.Code im] [PackedBlocks.Code im] {sk : BitVec 256}
theorem tb_halfHash_bind' {β : Type} {s : MachineState} {input : List UInt8} {W : Nat} (high : Bool)
    {f : Digest → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch im s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (pad64 input))
    (h : ∀ a : BitVec 256, TBSim im sk (writeHash s a) W (f (ClaudeWCT.WCT9.halfOf high a)) Q) :
    TBSim im sk s (8 * (toQ (pad64 input)).blocks + W) (ClaudeWCT.WCT9.halfHash high input >>= f) Q := by
  rw [ClaudeWCT.WCT9.halfHash_eq, bind_assoc]
  simp only [pure_bind]
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
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
/-- The step at which a G chain writes LOW (T51 top: `gTerm`; lower: 6). -/
def gTermL (lay : Layer) (i : Nat) : Nat := if lay = 0 then SharedRecover.gTerm i else SigGolfCandidate.T3.maxDigit lay i - 1
/-- Witness stack: on a G chain (lower odd, or top even `≤ 50`) the step keeps the high half exactly when it is not the
step `gTermL` (T51: `maxDigit - 1`; top chain 0 keeps the high half on every step). -/
theorem gHigh_eq {lay : Layer} {i m : Nat} (hG : ClaudeWCT.WCT9.isG lay i = true)
    (hm : m < SigGolfCandidate.T3.maxDigit lay i) :
    ClaudeWCT.WCT9.chainHigh lay i m = decide (m ≠ gTermL lay i) := by
  apply Bool.eq_iff_iff.mpr
  rw [ClaudeWCT.WCT9.chainHigh_eq_true, decide_eq_true_iff]
  rcases ClaudeWCT.WCT9.isG_eq_true.mp hG with ⟨hl, hi⟩ | ⟨hl, hi, hi50⟩
  · have hmd : SigGolfCandidate.T3.maxDigit lay i = 7 := by simp [SigGolfCandidate.T3.maxDigit, hl]
    have hg : gTermL lay i = 6 := by simp [gTermL, hl, hmd]
    rw [hmd] at hm
    rw [hg]
    constructor
    · rintro (⟨_, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h, _, _⟩)
      · omega
      · omega
      · exact absurd h hl
    · intro h; exact Or.inl ⟨hl, Or.inr ⟨hi, by omega⟩⟩
  · subst hl
    have hg : gTermL 0 i = SharedRecover.gTerm i := by simp [gTermL]
    rw [hg]
    unfold SharedRecover.gTerm
    constructor
    · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
      · exact absurd rfl h
      · by_cases h0 : i = 0
        · rw [if_pos h0]
          have : SigGolfCandidate.T3.maxDigit 0 i = 5 := by subst h0; rfl
          omega
        · rw [if_neg h0]; omega
    · intro h
      refine Or.inr ⟨rfl, ⟨hi, hi50⟩, ?_⟩
      by_cases h0 : i = 0
      · exact Or.inr h0
      · rw [if_neg h0] at h; exact Or.inl (by omega)

/-- Witness stack: one chain step (loop head 1031, header 1032..1040, the step block 49300..49337 and, on the F
path, the C3 tail) computes `halfHash (chainHigh) (chainInputW)`; at most 60 instructions + HASH. -/
theorem chain_step (lay : Layer) (tree leaf i st e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hst : st < e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 st)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t (stepW lay) (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st)
        (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v))
      (fun v' u => u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  have hlay := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) t hpc st e (by omega) (by omega) h20 h21
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, a28, m16, m24, r2, f2⟩ := rl1032_spec (im := im) t1 p1 lay tree leaf i st hr hf hi (by omega)
    (by rw [r1.get (by simp)]; exact hc.x8) (by rw [r1.get (by simp)]; exact hc.x19)
    (by rw [r1.get (by simp)]; exact hc.x9) (by rw [r1.get (by simp)]; exact hc.x18)
    (by rw [r1.get (by simp)]; exact h20)
  have f12 : Frame t t2 (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := (f1.trans f2).mono (fun A _ h => by
    rcases h with h | h; exact h.elim; exact h)
  have r12 : RegsExcept t t2 [.x6, .x7, .x10, .x11, .x12, .x28, .x30] := (r1.trans r2).mono (by simp)
  have g2 : ∀ r, r ∉ stepRegs → t2.getReg r = t.getReg r := fun r hr =>
    r12.get (not_mem_of_sub (by simp [stepRegs]) hr)
  obtain ⟨u0, s0, p0, r0, f0⟩ := sel_spec (im := im) t2 p2 lay.val (by omega)
    (by rw [g2 _ (by simp [stepRegs])]; exact hc.x8)
  have g19 : u0.getReg .x19 = BitVec.ofNat 64 i := by
    rw [r0.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x19
  have hK := expHdrK_le lay
  have fin_frame : ∀ {w : MachineState}, Frame t2 w (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) →
      Frame t w StepW := fun hw => (f12.trans hw).mono (fun A _ h => by
        unfold StepW; rcases h with h | h
        · exact Or.inl h
        · exact Or.inr h)
  rw [show ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v) =
    (ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i st) (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)
      >>= pure) by rw [bind_pure]]
  by_cases hGb : ClaudeWCT.WCT9.isG lay i = true
  · -- G path: `value | header | 0 | 0` at CHAIN+48
    obtain ⟨u, k1, su, hk1, upc, u6, u7, ur, uf⟩ : ∃ u k1, Steps im t2 k1 k1 u ∧ expHdrK lay + k1 + 23 ≤ stepW lay ∧
        u.pc = pcOf 49316 ∧ u.getReg .x6 = BitVec.ofNat 64 (gTermL lay i) ∧
        u.getReg .x7 = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
        RegsExcept t2 u [.x6, .x7] ∧ Frame t2 u (fun _ => False) := by
      rcases ClaudeWCT.WCT9.isG_eq_true.mp hGb with ⟨hl, hi2⟩ | ⟨hl, hi2, hi52⟩
      · have hl' : lay.val ≠ 0 := fun h => hl (Fin.ext h)
        rw [if_neg hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        rw [if_neg (by omega)] at p1'
        obtain ⟨u2, q2, p2', x6', x7', r2', f2'⟩ := lg_spec (im := im) u1 p1'
        refine ⟨u2, 7, s0.trans (q1.trans q2), by unfold stepW; rw [if_neg hl]; have := expHdrK_le lay; unfold expHdrK at this ⊢; split_ifs at this ⊢ <;> omega, p2', ?_, ?_, ?_, ?_⟩
        · rw [x6']; simp [gTermL, SigGolfCandidate.T3.maxDigit, hl]
        · rw [x7', Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi (by omega)]
        · exact ((r0.trans r1').trans r2').mono (by simp)
        · exact ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
      · have hl' : lay.val = 0 := by rw [hl]; rfl
        rw [if_pos hl'] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        rw [if_pos hi2] at p1'
        obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
          (by rw [r1'.get (by simp)]; exact g19)
        rw [if_neg (by omega)] at p2'
        obtain ⟨u3, q3, p3', x6', x7', r3', f3'⟩ := tcap_spec (im := im) u2 p2' i (by omega) hi2
          (by rw [r2'.get (by simp), r1'.get (by simp)]; exact g19)
          (by rw [r2'.get (by simp), r1'.get (by simp), r0.get (by simp)]; exact a28)
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl']
        refine ⟨u3, _, ((s0.trans q1).trans q2).trans q3, by rw [hK0]; unfold stepW gtK; rw [if_pos hl]; split_ifs <;> omega,
          p3', ?_, ?_, ?_, ?_⟩
        · rw [x6', hl]; simp [gTermL]
        · have f02 : Frame t2 u2 (fun _ => False) :=
            ((f0.trans f1').trans f2').mono (fun A _ h => by simp_all)
          rw [x7', f02.get (by decide) (by simp), m24]
        · exact (((r0.trans r1').trans r2').trans r3').mono (by simp)
        · exact (((f0.trans f1').trans f2').trans f3').mono (fun A _ h => by simp_all)
    have g1 : ∀ r, r ∉ [Reg.x6, .x7] → u.getReg r = t2.getReg r := fun r hr => ur.get hr
    have hT : gTermL lay i < 2 ^ 63 := by
      unfold gTermL SharedRecover.gTerm SigGolfCandidate.T3.maxDigit; split_ifs <;> omega
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u264, u272, u280, u288, u296, u2104, u2r, u2f⟩ :=
      g_spec (im := im) u upc st (gTermL lay i) _ (by omega) hT u6 u7
        (by rw [g1 _ (by simp), r12.get (by simp)]; exact h20) (by rw [g1 _ (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => CHAIN + 64 ≤ A ∧ A < CHAIN + 112) :=
      (uf.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12, .x30] := (ur.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have hq : hashInput u2 = toQ (pad64 (ClaudeWCT.WCT9.chainInputW lay tree leaf i st v)) := by
      have hl := ClaudeWCT.WCT9.chainInputW_length lay tree leaf i st v
      rw [pad64_of_aligned _ (by rw [hl])]
      refine hashInput_toQ u2 _ 0 (CHAIN + 48) hl u210 (by decide) (by decide) u211 (by decide) ?_
      rw [wordsOf_chainInputW_G hGb, readWords_eight]
      rw [show CHAIN + 48 + 8 = CHAIN + 56 from rfl, show CHAIN + 48 + 16 = CHAIN + 64 from rfl,
        show CHAIN + 48 + 24 = CHAIN + 72 from rfl, show CHAIN + 48 + 32 = CHAIN + 80 from rfl,
        show CHAIN + 48 + 40 = CHAIN + 88 from rfl, show CHAIN + 48 + 48 = CHAIN + 96 from rfl,
        show CHAIN + 48 + 56 = CHAIN + 104 from rfl]
      rw [v2.1, v2.2, u264, u272, u280, u288, u296, u2104, uf.get (A := CHAIN + 16) (by decide) (by simp), m16]
    have hvalid : hashArgumentsValid u2 = true := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 48) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
      · rw [if_neg hm6] at u212
        exact hashArgs_const u2 (CHAIN + 48) 64 (CHAIN + 32) u210 u211 u212 (by decide) (by decide) (by decide)
          (by decide) (by decide)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2) _ (fetch_49328 (im := im) u2 u2pc) h5' hvalid hq (fun a => ?_))).mono
      (by rw [chainInputW_blocks]; split_ifs <;> omega) (fun _ _ h => h)
    have hw20 : (writeHash u2 a).getReg .x20 = BitVec.ofNat 64 st := by
      rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]
      exact h20
    obtain ⟨w, sw, wpc, w20, wr, wf⟩ := gtail_spec (im := im) (writeHash u2 a)
      (by rw [pc_writeHash, u2pc, pcOf_add4]) st hw20
    have hB : ∀ B, u2.getReg .x12 = BitVec.ofNat 64 B → B = CHAIN + 32 ∨ B = CHAIN + 48 →
        Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := fun B h12 hB =>
      (Frame.writeHash u2 a B h12 (by rcases hB with rfl | rfl <;> decide)).mono
        (fun A _ h => by simp only [CHAIN] at hB ⊢; omega)
    have hwf : Frame u2 (writeHash u2 a) (fun A => CHAIN + 32 ≤ A ∧ A < CHAIN + 112) := by
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212; exact hB _ u212 (Or.inr rfl)
      · rw [if_neg hm6] at u212; exact hB _ u212 (Or.inl rfl)
    have hval : DigAt (writeHash u2 a) (CHAIN + 48)
        (ClaudeWCT.WCT9.halfOf (ClaudeWCT.WCT9.chainHigh lay i st) a) := by
      rw [gHigh_eq hGb (by omega)]
      by_cases hm6 : st = gTermL lay i
      · rw [if_pos hm6] at u212
        rw [decide_eq_false (fun h => h hm6)]
        exact DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by decide)
      · rw [if_neg hm6] at u212
        rw [decide_eq_true hm6]
        exact DigAt.writeHash_hi u2 a (CHAIN + 32) u212 (by decide)
    have fall : Frame t w StepW := fin_frame (((f02.trans hwf).trans wf).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; rcases h with (h | h) | h <;> first | omega | exact h.elim))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      have rr : RegsExcept u2 (writeHash u2 a) [] := fun r _ => getReg_writeHash u2 a r
      rw [((r02.trans rr).trans wr).get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    refine TBSim.steps (W := 0) sw (TBSim.pure ⟨wpc, w20, ?_, ?_, hval.frame wf (by decide) (by simp) (by simp),
      rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
  · -- F path: `T3.chainInput` at CHAIN
    have hGf : ClaudeWCT.WCT9.isG lay i = false := by simpa using hGb
    rw [ClaudeWCT.WCT9.chainInputW_F hGf]
    obtain ⟨u1, k1, su1, hk1, u1pc, u1r, u1f⟩ : ∃ u1 k1, Steps im t2 k1 k1 u1 ∧
        expHdrK lay + k1 + trXE lay.val i st ≤ 43 ∧ u1.pc = pcOf 49331 ∧ RegsExcept t2 u1 [.x6, .x7] ∧
        Frame t2 u1 (fun _ => False) := by
      by_cases hl0 : lay.val = 0
      · rw [if_pos hl0] at p0
        have hl : lay = 0 := Fin.ext hl0
        have hK0 : expHdrK lay = 25 := by unfold expHdrK; rw [if_pos hl0]
        obtain ⟨u1, q1, p1', r1', f1'⟩ := tsel_spec (im := im) u0 p0 i (by omega) g19
        by_cases hi2 : i % 2 = 0
        · rw [if_pos hi2] at p1'
          obtain ⟨u2, q2, p2', r2', f2'⟩ := tle_spec (im := im) u1 p1' i (by omega)
            (by rw [r1'.get (by simp)]; exact g19)
          exact absurd (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inr ⟨hl, hi2, hiT hl⟩)) hGb
        · rw [if_neg hi2] at p1'
          have hX : trXE lay.val i st = 2 := by unfold trXE; rw [if_pos (by omega)]
          exact ⟨u1, 5, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
            (f0.trans f1').mono (fun A _ h => by simp_all)⟩
      · rw [if_neg hl0] at p0
        obtain ⟨u1, q1, p1', r1', f1'⟩ := lsel_spec (im := im) u0 p0 i g19
        have hi2 : i % 2 = 0 := by
          by_contra h
          exact hGb (ClaudeWCT.WCT9.isG_eq_true.mpr (Or.inl ⟨fun h' => hl0 (by rw [h']; rfl), by omega⟩))
        rw [if_pos hi2] at p1'
        have := trXE_le lay.val i st
        exact ⟨u1, 4, s0.trans q1, by omega, p1', (r0.trans r1').mono (by simp),
          (f0.trans f1').mono (fun A _ h => by simp_all)⟩
    obtain ⟨u2, su2, u2pc, u210, u211, u212, u232, u240, u2r, u2f⟩ :=
      f_spec (im := im) u1 u1pc (by rw [u1r.get (by simp)]; exact a28)
    have f02 : Frame t2 u2 (fun A => A = CHAIN + 32 ∨ A = CHAIN + 40) :=
      (u1f.trans u2f).mono (fun A _ h => by rcases h with h | h <;> simp_all)
    have r02 : RegsExcept t2 u2 [.x6, .x7, .x10, .x11, .x12] := (u1r.trans u2r).mono (by simp)
    have v2 := (hv.frame f12 (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)).frame f02
      (by decide) (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)
    have z0 : u2.getMem (BitVec.ofNat 64 CHAIN) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z0
    have z8 : u2.getMem (BitVec.ofNat 64 (CHAIN + 8)) = 0 := by
      rw [f02.get (by decide) (by simp only [CHAIN]; omega), f12.get (by decide) (by simp only [CHAIN]; omega)]
      exact hc.z8
    have hq : hashInput u2 = toQ (pad64 (chainInput lay tree leaf i st v)) := by
      refine hashInput_toQ u2 _ 0 CHAIN (by rw [pad64_of_aligned _ (by rw [chainInput_length']), chainInput_length'])
        u210 (by simp only [CHAIN]) (by simp only [CHAIN]; omega) u211 (by norm_num) ?_
      rw [readWords_eight, wordsOf_chainInput', z0, z8,
        f02.get (A := CHAIN + 16) (by decide) (by simp only [CHAIN]; omega),
        f02.get (A := CHAIN + 24) (by decide) (by simp only [CHAIN]; omega), m16, m24, u232, u240, v2.1,
        show CHAIN + 48 + 8 = CHAIN + 56 from rfl, v2.2]
    have hvalid : hashArgumentsValid u2 = true :=
      hashArgs_const u2 CHAIN 64 (CHAIN + 48) u210 u211 u212 (by simp only [CHAIN]) (by norm_num)
        (by simp only [CHAIN]; omega) (by simp only [CHAIN]) (by simp only [CHAIN]; omega)
    have h5' : u2.getReg .x5 = 0 := by rw [r02.get (by simp), g2 _ (by simp [stepRegs])]; exact hc.x5
    refine (TBSim.steps (((s1.trans s2).trans su1).trans su2)
      (tb_halfHash_bind' (im := im) (W := 2 + trXE lay.val i st) _ (fetch_49336 (im := im) u2 u2pc) h5' hvalid hq
        (fun a => ?_))).mono
      (by rw [blocks_chainInput']; unfold stepW; split_ifs <;> omega) (fun _ _ h => h)
    have gw : ∀ r, r ∉ stepRegs → (writeHash u2 a).getReg r = t.getReg r := fun r hr => by
      rw [getReg_writeHash, r02.get (by simp [stepRegs] at hr ⊢; tauto), g2 r hr]
    have p3 : (writeHash u2 a).pc = pcOf 49337 := by rw [pc_writeHash, u2pc, pcOf_add4]
    have hlo := DigAt.writeHash_lo u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have hhi : DigAt (writeHash u2 a) (CHAIN + 64) (a.extractLsb' 128 128) :=
      DigAt.writeHash_hi u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    obtain ⟨w, s4, p4, w20, hd, r4, f4⟩ := rl1047_spec (im := im) (writeHash u2 a) p3 lay i st (by omega) (by omega)
      hGf (by rw [gw _ (by simp [stepRegs])]; exact hc.x8) (by rw [gw _ (by simp [stepRegs])]; exact hc.x19)
      (by rw [getReg_writeHash, r02.get (by simp), r12.get (by simp)]; exact h20) _ _ hlo hhi
    have fw := Frame.writeHash u2 a (CHAIN + 48) u212 (by simp only [CHAIN]; omega)
    have fall : Frame t w StepW := fin_frame (((f02.trans fw).trans f4).mono (fun A _ h => by
      simp only [CHAIN] at h ⊢; omega))
    have rall : RegsExcept t w stepRegs := fun r hr => by
      rw [r4.get (not_mem_of_sub (by simp [stepRegs]) hr), gw r hr]
    refine TBSim.steps (W := 0) s4 (TBSim.pure ⟨p4, w20, ?_, ?_, ?_, rall, fall⟩)
    · rw [rall.get (by simp [stepRegs])]; exact h21
    · exact hc.frame (l := stepRegs) (by simp [stepRegs]) rall fall
    · unfold ClaudeWCT.WCT9.halfOf; exact hd

theorem chain_loop (lay : Layer) (tree leaf i d e : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hd : d ≤ e) (he : e ≤ 7)
    (hcap : e ≤ SigGolfCandidate.T3.maxDigit lay i)
    (hi : i < 64) (hiT : lay = 0 → i ≤ 50) (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1031)
    (hc : ChainCtx lay.val tree leaf i t) (h20 : t.getReg .x20 = BitVec.ofNat 64 d)
    (h21 : t.getReg .x21 = BitVec.ofNat 64 e) (hv : DigAt t (CHAIN + 48) v) :
    TBSim im sk t ((e - d) * stepW lay + 1) (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v)
      (fun v' u => u.pc = pcOf 1049 ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
        ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) v' ∧ RegsExcept t u stepRegs ∧ Frame t u StepW) := by
  let Inv : Nat → Digest → MachineState → Prop := fun j w u =>
    u.pc = pcOf 1031 ∧ u.getReg .x20 = BitVec.ofNat 64 (d + j) ∧ u.getReg .x21 = BitVec.ofNat 64 e ∧
      ChainCtx lay.val tree leaf i u ∧ DigAt u (CHAIN + 48) w ∧ RegsExcept t u stepRegs ∧ Frame t u StepW
  have hloop := TBSim.foldlM_range' (image := im) (sk := sk) d (e - d)
    (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v Inv (stepW lay)
    (fun j hj w u hu => by
      obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
      refine (chain_step (im := im) lay tree leaf i (d + j) e hr hf (by omega) he hcap hi hiT w u p cc x20 x21 dv).mono le_rfl ?_
      rintro w' u' ⟨p', y20, y21, cc', dv', rr', ff'⟩
      refine ⟨p', by rw [y20]; congr 1, y21, cc', dv', ?_, ?_⟩
      · exact (rr.trans rr').mono (fun r hr => by
          rcases List.mem_append.mp hr with h | h <;> exact h)
      · exact (ff.trans ff').mono (fun A _ h => by rcases h with h | h <;> exact h))
    (s := t) ⟨hpc, by simpa using h20, h21, hc, hv, RegsExcept.refl _ _, Frame.refl _ _⟩
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v = ((List.range' d (e - d)).foldlM
      (fun value step => ClaudeWCT.WCT9.halfHash (ClaudeWCT.WCT9.chainHigh lay i step) (ClaudeWCT.WCT9.chainInputW lay tree leaf i step value)) v >>= pure) := by
    rw [bind_pure]; rfl
  rw [hprog]
  refine (TBSim.bind (W₂ := 1) hloop (fun w u hu => ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨p, x20, x21, cc, dv, rr, ff⟩ := hu
  obtain ⟨u1, s1, p1, r1, f1⟩ := rl1031_spec (im := im) u p (d + (e - d)) e (by omega) (by omega) x20 x21
  rw [if_pos (by omega)] at p1
  exact (TBSim.steps s1 (TBSim.pure ⟨p1, by rw [r1.get (by simp)]; exact x21, cc.frame (l := []) (by simp) r1
      (f1.mono (fun _ _ h => h.elim)), dv.frame f1 (by simp only [CHAIN]; omega) (by simp) (by simp),
    (rr.trans r1).mono (by simp), (ff.trans f1).mono (fun A _ h => by rcases h with h | h; exact h; exact h.elim)⟩)).mono
    (by omega) (fun _ _ h => h)

theorem endpoint_top (i n4 : Nat) : SigGolfCandidate.T3.maxDigit 0 i = endpoint 0 i n4 := by
  simp [SigGolfCandidate.T3.maxDigit, endpoint]

theorem rl_one (lay : Layer) (tree leaf i d P W n n4 : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 31) (hf : leaf < 2 ^ T3.height lay) (hi : i < n) (hn : n ≤ 58)
    (hiT : lay = 0 → i ≤ 50)
    (hn4 : n4 ≤ n) (hP : 0x7000 ≤ P) (hPi : P + 16 * i + 16 ≤ 0x7000 + 5616) (hP8 : P % 8 = 0)
    (hW8 : W % 8 = 0) (hW : 64 ≤ W) (hW' : W + 64 ≤ 0x7000) (hd : d ≤ (endpoint lay i n4))
    (hcap : endpoint lay i n4 ≤ SigGolfCandidate.T3.maxDigit lay i)
    (v : Digest) (t : MachineState) (hpc : t.pc = pcOf 1010)
    (hc : ChainCtx lay.val tree leaf i t) (h26 : t.getReg .x26 = BitVec.ofNat 64 n)
    (h27 : t.getReg .x27 = BitVec.ofNat 64 n4) (h16 : t.getReg .x16 = BitVec.ofNat 64 P)
    (h23 : t.getReg .x23 = BitVec.ofNat 64 W) (hv : DigAt t (P + 16 * i) v)
    (hdig : t.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    TBSim im sk t 461 (ClaudeWCT.WCT9.chainW lay tree leaf i d ((endpoint lay i n4) - d) v)
      (fun v' u => u.pc = pcOf 1010 ∧ u.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
        u.getReg .x23 = BitVec.ofNat 64 (W - 64) ∧ ChainCtx lay.val tree leaf (i + 1) u ∧
        DigAt u (LEAFPK + slotOff lay i) v' ∧ DigAt u (W + 48) v ∧ RegsExcept t u oneRegs ∧ Frame t u (OneW lay i W)) := by
  have hlay := lay.isLt
  set e := (endpoint lay i n4) with he
  have he7 : e ≤ 7 := by rw [he]; unfold endpoint; split_ifs <;> omega
  obtain ⟨t1, s1, p1, r1, f1⟩ := rl1010_spec (im := im) t hpc i n (by omega) (by omega) hc.x19 h26
  rw [if_neg (by omega)] at p1
  obtain ⟨t2, s2, p2, c48, c56, w48, w56, x23, x28, r2, f2⟩ := rl1011_spec (im := im) t1 p1 i P W hP hPi hP8 hW8 hW hW'
    (by rw [r1.get (by simp)]; exact hc.x19) (by rw [r1.get (by simp)]; exact h16)
    (by rw [r1.get (by simp)]; exact h23)
  have f12 : Frame t t2 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (f1.trans f2).mono (fun A _ h => by rcases h with h | h; exact h.elim; exact h)
  have hb2 : t2.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d := by
    rw [Frame.getByte f12 (by simp only [DIGITS]; omega) (by simp only [DIGITS, CHAIN]; omega), hdig]
  obtain ⟨t3, s3, p3, x20, r3, f3⟩ := rl1027_spec (im := im) t2 p2 i d (by omega) (by omega) x28 hb2
  obtain ⟨t4, s4, p4, x21, r4, f4⟩ := rl1028_spec (im := im) t3 p3 lay.val (by omega)
    (by rw [r3.get (by simp), r2.get (by simp), r1.get (by simp)]; exact hc.x8)
  obtain ⟨t5, s5, p5, x21', r5, f5⟩ : ∃ t5, Steps im t4 (endpointExtra lay i n4) (endpointExtra lay i n4) t5 ∧
      t5.pc = pcOf 1031 ∧ t5.getReg .x21 = BitVec.ofNat 64 e ∧ RegsExcept t4 t5 [.x21, .x28] ∧
      Frame t4 t5 (fun _ => False) := by
    have hl0 : lay.val = 0 ↔ lay = 0 := by simp
    by_cases hl : lay = 0
    · rw [if_pos (hl0.mpr hl)] at p4
      obtain ⟨ta, qa, pa, ra, fa⟩ := rl1030_spec (im := im) t4 p4
      have rr := (((r1.trans r2).trans r3).trans r4).trans ra
      obtain ⟨tb, qb, pb, xb, rb, fb⟩ := rl1158_spec (im := im) ta pa i (by omega)
        (by rw [rr.get (by simp)]; exact hc.x19)
      refine ⟨tb, ?_, pb, ?_, ?_, ?_⟩
      · simpa only [endpointExtra, if_pos hl] using qa.trans qb
      · rw [xb, he, hl, ← endpoint_top i n4]
      · exact (ra.trans rb).mono (by simp)
      · exact (fa.trans fb).mono (by simp)
    · rw [if_neg (fun hv => hl (hl0.mp hv))] at p4
      exact ⟨t4, by simpa [endpointExtra, hl] using Steps.refl t4, p4,
        by simpa [he, endpoint, hl] using x21, RegsExcept.refl _ _, Frame.refl _ _⟩
  have f15 : Frame t t5 (fun A => A = CHAIN + 48 ∨ A = CHAIN + 56 ∨ A = W + 48 ∨ A = W + 56) :=
    (((f12.trans f3).trans f4).trans f5).mono (fun A _ h => by
      rcases h with ((h | h) | h) | h
      · exact h
      · exact h.elim
      · exact h.elim
      · exact h.elim)
  have r15 : RegsExcept t t5 ([] ++ [.x6, .x7, .x23, .x28, .x29, .x30] ++ [.x20] ++ [.x21] ++ [.x21, .x28]) :=
    (((r1.trans r2).trans r3).trans r4).trans r5
  have g5 : ∀ r, r ∉ [Reg.x6, .x7, .x20, .x21, .x23, .x28, .x29, .x30] → t5.getReg r = t.getReg r :=
    fun r hr => r15.get (fun hm => hr (by simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; tauto))
  have hc5 : ChainCtx lay.val tree leaf i t5 :=
    { x5 := by rw [g5 _ (by simp)]; exact hc.x5
      x8 := by rw [g5 _ (by simp)]; exact hc.x8
      x9 := by rw [g5 _ (by simp)]; exact hc.x9
      x18 := by rw [g5 _ (by simp)]; exact hc.x18
      x19 := by rw [g5 _ (by simp)]; exact hc.x19
      z0 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z0
      z8 := by rw [f15.get (by simp only [CHAIN]; omega) (by simp only [CHAIN]; omega)]; exact hc.z8 }
  have hv5 : DigAt t5 (CHAIN + 48) v := by
    constructor
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c48, f1.get (by omega) (by simp)]; exact hv.1
    · rw [f5.get (by simp only [CHAIN]; omega) (by simp), f4.get (by simp only [CHAIN]; omega) (by simp),
        f3.get (by simp only [CHAIN]; omega) (by simp), c56, f1.get (by omega) (by simp)]; exact hv.2
  have x20' : t5.getReg .x20 = BitVec.ofNat 64 d := by rw [r5.get (by simp), r4.get (by simp)]; exact x20
  have hloop := chain_loop (im := im) (sk := sk) lay tree leaf i d e hr hf hd he7 hcap (by omega) hiT v t5 p5 hc5 x20' x21' hv5
  have hprog : ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v =
      (ClaudeWCT.WCT9.chainW lay tree leaf i d (e - d) v >>= pure) := by rw [bind_pure]
  rw [hprog]
  have total_cost : (1 + 16 + 1 + 2 + endpointExtra lay i n4) + ((e - d) * stepW lay + 1 + 17) ≤ 461 := by
    rw [he]; unfold endpointExtra endpoint stepW SharedRecover.kmaxSteps
    split_ifs <;> omega
  refine (TBSim.steps (((((s1.trans s2).trans s3).trans s4).trans s5)) (TBSim.bind (W₂ := 17) hloop
    (fun v' u hu => ?_))).mono (by
      simpa only [Nat.add_assoc] using total_cost) (fun _ _ h => h)
  obtain ⟨pu, u21, cu, du, ru, fu⟩ := hu
  obtain ⟨u2, q2, pu2, z28, ry2, fy2⟩ := rl1049_spec (im := im) u pu lay i (by omega) cu.x8 cu.x19
  have hslot8 : slotOff lay i % 8 = 0 := by unfold slotOff; split_ifs <;> omega
  have hslot : LEAFPK + slotOff lay i + 16 ≤ 2 ^ 24 := by unfold slotOff; simp only [LEAFPK]; split_ifs <;> omega
  obtain ⟨u3, q3, pu3, w19, m0, m8, ry3, fy3⟩ := rl1052_spec (im := im) u2 pu2 i (slotOff lay i) hslot8 hslot z28
    (by rw [ry2.get (by simp)]; exact cu.x19)
  have fy12 : Frame u u2 (fun _ => False) := fy2
  have hslotC : ∀ A, (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) → ¬ StepW A := by
    intro A hA hS; unfold StepW at hS; unfold slotOff at hA; simp only [LEAFPK, CHAIN] at hA hS; split_ifs at hA <;> omega
  refine (TBSim.steps (q2.trans q3) (TBSim.pure ⟨pu3, w19, ?_, ?_, ?_, ?_, ?_, ?_⟩)).mono
    (by unfold slK; split_ifs <;> omega) (fun _ _ h => h)
  · rw [ry3.get (by simp), ry2.get (by simp), ru.get (by simp [stepRegs]),
      r5.get (by simp), r4.get (by simp), r3.get (by simp)]; exact x23
  · refine
      { x5 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x5
        x8 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x8
        x9 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x9
        x18 := by rw [ry3.get (by simp), ry2.get (by simp)]; exact cu.x18
        x19 := w19
        z0 := ?_, z8 := ?_ } <;>
    · rw [fy3.get (by simp only [CHAIN]; omega) (by unfold slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega),
        fy12.get (by simp only [CHAIN]; omega) (by simp)]
      first | exact cu.z0 | exact cu.z8
  · constructor
    · rw [m0, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.1
    · rw [m8, fy12.get (by simp only [CHAIN]; omega) (by simp)]; exact du.2
  · have hW : ∀ A, (A = W + 48 ∨ A = W + 56) → A < 2 ^ 64 ∧ ¬ StepW A ∧ ¬ (A = LEAFPK + slotOff lay i ∨ A = LEAFPK + slotOff lay i + 8) := by
      intro A hA; unfold StepW slotOff; simp only [LEAFPK, CHAIN]; split_ifs <;> omega
    constructor
    · obtain ⟨h1, h2, h3⟩ := hW (W + 48) (Or.inl rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w48, f1.get (by omega) (by simp)]; exact hv.1
    · obtain ⟨h1, h2, h3⟩ := hW (W + 56) (Or.inr rfl)
      rw [fy3.get h1 h3, fy12.get h1 (by simp), fu.get h1 h2, f5.get h1 (by simp), f4.get h1 (by simp),
        f3.get h1 (by simp), w56, f1.get (by omega) (by simp)]; exact hv.2
  · intro r hr
    have hr' : r ∉ [Reg.x6, .x7, .x10, .x11, .x12, .x19, .x20, .x21, .x23, .x28, .x29, .x30] := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [ry3.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ry2.get (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      ru.get (by simp only [stepRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto),
      g5 r (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; tauto)]
  · intro A hA hn
    unfold OneW at hn
    simp only [not_or] at hn
    rw [fy3.get hA (by tauto), fy12.get hA (by simp), fu.get hA hn.1,
      f15.get hA (by simp only [CHAIN] at hn ⊢; unfold StepW at hn; simp only [CHAIN] at hn; omega)]

end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_LayersBlocks ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
set_option autoImplicit false
set_option maxRecDepth 8192
abbrev IDXV : Nat := 0x20550
theorem shr_and_mask (a k m : Nat) (ha : a < 2 ^ 64) (hm : m ≤ 64) :
    BitVec.ofNat 64 a >>> k &&& BitVec.ofNat 64 (2 ^ m - 1) = BitVec.ofNat 64 (a / 2 ^ k % 2 ^ m) := by
  rw [ofNat_shr _ _ ha, ofNat_and_mask _ _ hm]
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
def lE (lay : Layer) : Nat := ![318, 295, 272, 249] lay
def lK (lay : Layer) : Nat := ![14, 13, 13, 13] lay
def lR1 (lay : Layer) : Nat := ![332, 308, 285, 262] lay
def lR2 (lay : Layer) : Nat := ![342, 318, 295, 272] lay
def lD (lay : Layer) : Nat := ![0x3ce8, 0x4968, 0x55a8, 0x820] lay
def lk (lay : Layer) : Nat := ![0, 0, 0, 0] lay
def lP (lay : Layer) : Nat := ![0x7890, 0x7cb0, 0x7fd0, 0x82e0] lay
def lWC (lay : Layer) : Nat := ![0x3c88, 0x4908, 0x5548, 0x6188] lay
def lWM (lay : Layer) : Nat := ![0x2f08, 0x3e48, 0x4A88, 0x56C8] lay
theorem route_fst (index : Nat) (lay : Layer) :
    (route index lay).1 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay) % 2 ^ height lay := rfl
theorem route_snd (index : Nat) (lay : Layer) :
    (route index lay).2 = index / 2 ^ ((![19, 12, 6, 0] : Layer → Nat) lay + height lay) := rfl
end SigGolfCandidate.T3M.Expand

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Layer route height chainCount target)
open SigGolfCandidate.T3M.Search (ENC csN4 ofNat_and_mask)
open SigGolfCandidate.T3M.Expand
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
def entryCode249 : List (BitVec 32) := seg_249.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock249 := symRun {noAlias := true} entryCode249 (pcOf 249) 200
def entryCode272 : List (BitVec 32) := seg_272.set 4 (0xc900893 : BitVec 32)
sym_block entryBlock272 := symRun {noAlias := true} entryCode272 (pcOf 272) 200
class EntryCode (im : Image) : Prop where
  code249 : CodeAt im (pcOf 249) entryCode249
  code272 : CodeAt im (pcOf 272) entryCode272
  code295 : CodeAt im (pcOf 295) seg_295
  code318 : CodeAt im (pcOf 318) seg_318
  code262 : CodeAt im (pcOf 262) seg_262
  code285 : CodeAt im (pcOf 285) seg_285
  code308 : CodeAt im (pcOf 308) seg_308
  code332 : CodeAt im (pcOf 332) seg_332
variable {im : Image} [EntryCode im]
section
variable (s : MachineState)
theorem l249_spec (hpc : s.pc = pcOf 249) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 262 ∧
      t.getReg .x8 = BitVec.ofNat 64 3 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 0 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 6) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock249 (EntryCode.code249 (im := im)) s hpc (by simp [entryBlock249.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock249.res, E.eval]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp [entryBlock249.res, rv_simp]
  · simp only [Result.toState_getReg, entryBlock249.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, entryBlock249.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs entryBlock249.res
  · intro A _ _; simp [entryBlock249.res, rv_simp]

theorem l272_spec (hpc : s.pc = pcOf 272) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 285 ∧
      t.getReg .x8 = BitVec.ofNat 64 2 ∧ t.getReg .x15 = BitVec.ofNat 64 6 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 6 % 2 ^ 6) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 12) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound entryBlock272 (EntryCode.code272 (im := im)) s hpc (by simp [entryBlock272.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, entryBlock272.res, E.eval]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp [entryBlock272.res, rv_simp]
  · simp only [Result.toState_getReg, entryBlock272.res, rv_simp, hidx]
    t3n []
    rw [show (63#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, entryBlock272.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs entryBlock272.res
  · intro A _ _; simp [entryBlock272.res, rv_simp]

theorem l295_spec (hpc : s.pc = pcOf 295) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 13 13 t ∧ t.pc = pcOf 457 ∧ t.getReg .x1 = pcOf 308 ∧
      t.getReg .x8 = BitVec.ofNat 64 1 ∧ t.getReg .x15 = BitVec.ofNat 64 7 ∧
      t.getReg .x26 = BitVec.ofNat 64 43 ∧ t.getReg .x27 = BitVec.ofNat 64 0 ∧
      t.getReg .x17 = BitVec.ofNat 64 201 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 12 % 2 ^ 7) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 19) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_295 (EntryCode.code295 (im := im)) s hpc (by simp [eblk_295.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_295.res, E.eval]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp [eblk_295.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [show (127#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 7 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_295.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_295.res
  · intro A _ _; simp [eblk_295.res, rv_simp]

theorem l318_spec (hpc : s.pc = pcOf 318) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s 14 14 t ∧ t.pc = pcOf 54522 ∧ t.getReg .x1 = pcOf 332 ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x15 = BitVec.ofNat 64 12 ∧
      t.getReg .x26 = BitVec.ofNat 64 51 ∧ t.getReg .x27 = BitVec.ofNat 64 51 ∧
      t.getReg .x17 = BitVec.ofNat 64 152 ∧
      t.getReg .x18 = BitVec.ofNat 64 (index / 2 ^ 19 % 2 ^ 12) ∧ t.getReg .x9 = BitVec.ofNat 64 (index / 2 ^ 31) ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_318 (EntryCode.code318 (im := im)) s hpc (by simp [eblk_318.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_318.res, E.eval]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp [eblk_318.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [show (4095#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 12 - 1) from rfl,
      shr_and_mask _ _ _ (by omega) (by decide)]
    norm_num
  · simp only [Result.toState_getReg, eblk_318.res, rv_simp, hidx]
    t3n []
    rw [ofNat_shr _ _ (by omega)]
    norm_num
  · ex_regs eblk_318.res
  · intro A _ _; simp [eblk_318.res, rv_simp]

theorem l262_spec (hpc : s.pc = pcOf 262) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 272 ∧
      t.getMem (BitVec.ofNat 64 0x820) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x820)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x82e0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x6188 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x56c8 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x820) := by
  refine ⟨_, symRun_sound eblk_262 (EntryCode.code262 (im := im)) s hpc (by simp [eblk_262.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_262.res, E.eval]
  · simp [eblk_262.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_262.res]
    t3n [h19]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · simp [eblk_262.res, rv_simp]
  · ex_regs eblk_262.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_262.res]
    t3n []
    rw [if_neg (by omega)]

theorem l285_spec (hpc : s.pc = pcOf 285) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 295 ∧
      t.getMem (BitVec.ofNat 64 0x55a8) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x55a8)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7fd0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x5548 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x4a88 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x55a8) := by
  refine ⟨_, symRun_sound eblk_285 (EntryCode.code285 (im := im)) s hpc (by simp [eblk_285.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_285.res, E.eval]
  · simp [eblk_285.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_285.res]
    t3n [h19]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · simp [eblk_285.res, rv_simp]
  · ex_regs eblk_285.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_285.res]
    t3n []
    rw [if_neg (by omega)]

theorem l308_spec (hpc : s.pc = pcOf 308) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 318 ∧
      t.getMem (BitVec.ofNat 64 0x4968) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x4968)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7cb0 ∧ t.getReg .x23 = BitVec.ofNat 64 0x4908 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x3e48 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x4968) := by
  refine ⟨_, symRun_sound eblk_308 (EntryCode.code308 (im := im)) s hpc (by simp [eblk_308.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_308.res, E.eval]
  · simp [eblk_308.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_308.res]
    t3n [h19]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · simp [eblk_308.res, rv_simp]
  · ex_regs eblk_308.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_308.res]
    t3n []
    rw [if_neg (by omega)]

theorem l332_spec (hpc : s.pc = pcOf 332) (c : Nat) (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf 342 ∧
      t.getMem (BitVec.ofNat 64 0x3ce8) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 0x3ce8)) 0 ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 0x7890 ∧ t.getReg .x23 = BitVec.ofNat 64 0x3c88 ∧
      t.getReg .x24 = BitVec.ofNat 64 0x2f08 ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = 0x3ce8) := by
  refine ⟨_, symRun_sound eblk_332 (EntryCode.code332 (im := im)) s hpc (by simp [eblk_332.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_332.res, E.eval]
  · simp [eblk_332.res, rv_simp]
  · simp only [Result.toState_getMem, eblk_332.res]
    t3n [h19]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · simp [eblk_332.res, rv_simp]
  · ex_regs eblk_332.res
  · intro A hA hn
    simp only [Result.toState_getMem, eblk_332.res]
    t3n []
    rw [if_neg (by omega)]
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces

end
theorem lentry_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lE lay)) (index : Nat) (hi : index < 2 ^ 31)
    (hidx : s.getMem (BitVec.ofNat 64 IDXV) = BitVec.ofNat 64 index) :
    ∃ t, Steps im s (lK lay) (lK lay) t ∧ t.pc = pcOf (if lay=0 then 54522 else 457) ∧ t.getReg .x1 = pcOf (lR1 lay) ∧
      t.getReg .x8 = BitVec.ofNat 64 lay.val ∧ t.getReg .x15 = BitVec.ofNat 64 (height lay) ∧
      t.getReg .x26 = BitVec.ofNat 64 (chainCount lay) ∧ t.getReg .x27 = BitVec.ofNat 64 (csN4 lay) ∧
      t.getReg .x17 = BitVec.ofNat 64 (if lay=0 then 152 else 201) ∧
      t.getReg .x18 = BitVec.ofNat 64 (route index lay).1 ∧ t.getReg .x9 = BitVec.ofNat 64 (route index lay).2 ∧
      RegsExcept s t [.x1, .x6, .x7, .x8, .x9, .x15, .x17, .x18, .x26, .x27, .x28] ∧
      Frame s t (fun _ => False) := by
  -- Campaign T51: the top entry (318) ends with `jal KCOPY` (54522); KCOPY then enters the counter search at 457.
  rw [route_fst, route_snd]
  fin_cases lay
  · exact l318_spec (im := im) s hpc index hi hidx
  · exact l295_spec (im := im) s hpc index hi hidx
  · exact l272_spec (im := im) s hpc index hi hidx
  · exact l249_spec (im := im) s hpc index hi hidx

theorem lpost_spec (lay : Layer) (s : MachineState) (hpc : s.pc = pcOf (lR1 lay)) (c : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 c) :
    ∃ t, Steps im s 10 10 t ∧ t.pc = pcOf 997 ∧ t.getReg .x1 = pcOf (lR2 lay) ∧
      t.getMem (BitVec.ofNat 64 (lD lay)) =
        replaceWord32 (s.getMem (BitVec.ofNat 64 (lD lay))) (lk lay) ((BitVec.ofNat 64 c).truncate 32) ∧
      t.getReg .x16 = BitVec.ofNat 64 (lP lay) ∧ t.getReg .x23 = BitVec.ofNat 64 (lWC lay) ∧
      t.getReg .x24 = BitVec.ofNat 64 (lWM lay) ∧
      RegsExcept s t [.x1, .x16, .x23, .x24, .x28] ∧ Frame s t (fun A => A = lD lay) := by
  fin_cases lay
  · exact l332_spec (im := im) s hpc c h19
  · exact l308_spec (im := im) s hpc c h19
  · exact l285_spec (im := im) s hpc c h19
  · exact l262_spec (im := im) s hpc c h19


end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
theorem installed_entry : EntryCode Images.expandImage := by
  constructor <;> apply codeAt_expand_current_chunk <;> decide +kernel

end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def headWords : List (BitVec 32) := [0x000a0eb7,0x00ffae37,0xe00e0e13,0x768e0f13]
def loopWords : List (BitVec 32) := [0xe3303,0x6eb023,0x8e0e13,0x8e8e93,0xffee68e3]
def tailWords : List (BitVec 32) := [0xb18cb06f]

sym_block loopRun := symRun { noAlias := true } loopWords (pcOf 54526) 50
sym_block headRun := symRun { noAlias := true } headWords (pcOf 54522) 10
sym_block tailRun := symRun { noAlias := true } tailWords (pcOf 54531) 10

theorem loop_regs (s : MachineState) :
    RegsExcept s (loopRun.res.toState s) [.x6,.x28,.x29] := by
  intro r hr; simp at hr; cases r <;> simp_all [loopRun.res, rv_simp] <;> rfl

theorem loop_step {im : Image} (hc : CodeAt im (pcOf 54526) loopWords)
    (s : MachineState) (hpc : s.pc = pcOf 54526) (S D F : Nat)
    (hS8 : S % 8 = 0) (hD8 : D % 8 = 0) (hS : S + 8 ≤ 2 ^ 24) (hD : D + 8 ≤ 2 ^ 24) (hF : F < 2 ^ 64)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 S) (h29 : s.getReg .x29 = BitVec.ofNat 64 D)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 F) :
    ∃ t, Steps im s 5 5 t ∧ t.pc = (if S + 8 < F then pcOf 54526 else pcOf 54531) ∧
      t.getReg .x28 = BitVec.ofNat 64 (S + 8) ∧ t.getReg .x29 = BitVec.ofNat 64 (D + 8) ∧
      t.getMem (BitVec.ofNat 64 D) = s.getMem (BitVec.ofNat 64 S) ∧
      RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => A = D) := by
  refine ⟨_, symRun_sound loopRun hc s hpc ?_, ?_, ?_, ?_, ?_, loop_regs s, ?_⟩
  · simp [loopRun.res, rv_simp, h28, h29, accessValid_iff, MEMORY_BYTES]
    omega
  · have hlt : (BitVec.ofNat 64 (S + 8)).ult (BitVec.ofNat 64 F) = decide (S + 8 < F) := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show S + 8 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt hF]
    simp only [Result.toState_pc, loopRun.res, E.eval, BinOp.eval, CmpOp.eval, h28, h30, ofNat_add_ofNat,
      ofNat_add8, ofNat_add8', hlt]
    by_cases h : S + 8 < F <;> simp [h] <;> rfl
  · simp only [Result.toState_getReg, loopRun.res, rv_simp, h28, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getReg, loopRun.res, rv_simp, h29, ofNat_add_ofNat, ofNat_add8, ofNat_add8']
  · simp only [Result.toState_getMem, loopRun.res]
    t3n [h28, h29]
    simp
  · intro A hA hne
    simp only [Result.toState_getMem, loopRun.res]
    t3n [h29]
    split_ifs with he
    · exfalso; apply hne; omega
    · rfl

/-- `n + 1` iterations of the copy loop, ascending, source `S`, destination `D`, end `S + 8 (n + 1)`. -/
theorem loop_copy {im : Image} (hc : CodeAt im (pcOf 54526) loopWords) :
    ∀ n (s : MachineState) (S D : Nat), S % 8 = 0 → D % 8 = 0 → S + 8 * (n + 1) ≤ 2 ^ 24 →
      D + 8 * (n + 1) ≤ S → s.pc = pcOf 54526 →
      s.getReg .x28 = BitVec.ofNat 64 S → s.getReg .x29 = BitVec.ofNat 64 D →
      s.getReg .x30 = BitVec.ofNat 64 (S + 8 * (n + 1)) →
      ∃ t, Steps im s (5 * (n + 1)) (5 * (n + 1)) t ∧ t.pc = pcOf 54531 ∧
        t.getReg .x28 = BitVec.ofNat 64 (S + 8 * (n + 1)) ∧
        t.getReg .x29 = BitVec.ofNat 64 (D + 8 * (n + 1)) ∧
        (∀ i, i ≤ n → t.getMem (BitVec.ofNat 64 (D + 8 * i)) = s.getMem (BitVec.ofNat 64 (S + 8 * i))) ∧
        RegsExcept s t [.x6,.x28,.x29] ∧ Frame s t (fun A => D ≤ A ∧ A < D + 8 * (n + 1)) := by
  intro n
  induction n with
  | zero =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨t, st, pt, r28, r29, mt, rt, ft⟩ := loop_step hc s hpc S D (S + 8 * (0 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    refine ⟨t, st, by simpa using pt, by simpa using r28, by simpa using r29, ?_, rt, ft.mono (by intro A _ h; omega)⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    simpa using mt
  | succ n ih =>
    intro s S D hS8 hD8 hS hD hpc h28 h29 h30
    obtain ⟨u, su, pu, u28, u29, mu, ru, fu⟩ := loop_step hc s hpc S D (S + 8 * (n + 1 + 1))
      hS8 hD8 (by omega) (by omega) (by omega) h28 h29 h30
    have hpu : u.pc = pcOf 54526 := by rw [pu, if_pos (by omega)]
    obtain ⟨t, ut, pt, t28, t29, mt, rt, ft⟩ := ih u (S + 8) (D + 8) (by omega) (by omega) (by omega) (by omega)
      hpu u28 u29 (by rw [ru.get (by decide), h30]; congr 1; ring)
    refine ⟨t, ?_, pt, by rw [t28]; congr 1; ring, by rw [t29]; congr 1; ring, ?_, (ru.trans rt).mono (by decide), ?_⟩
    · convert su.trans ut using 1 <;> ring
    · intro i hi
      rcases i with _ | i
      · rw [ft _ (by omega) (by omega)]
        simpa using mu
      · have h1 := mt i (by omega)
        rw [show D + 8 * (i + 1) = D + 8 + 8 * i by ring, h1, show S + 8 + 8 * i = S + 8 * (i + 1) by ring]
        exact fu _ (by omega) (by omega)
    · exact (fu.trans ft).mono (by intro A _ h; rcases h with h | h <;> omega)

theorem head_spec {im : Image} (hc : CodeAt im (pcOf 54522) headWords) (s : MachineState) (hpc : s.pc = pcOf 54522) :
    ∃ t, Steps im s 4 4 t ∧ t.pc = pcOf 54526 ∧ t.getReg .x28 = BitVec.ofNat 64 0xFF9E00 ∧
      t.getReg .x29 = BitVec.ofNat 64 0xA0000 ∧ t.getReg .x30 = BitVec.ofNat 64 0xFFA568 ∧
      RegsExcept s t [.x28,.x29,.x30] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound headRun hc s hpc (by simp [headRun.res, rv_simp]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · simp [headRun.res, rv_simp]
  · intro r hr; cases r <;> first | rfl | exact (hr (by decide)).elim
  · intro A _ _; simp [headRun.res, rv_simp]

theorem tail_spec {im : Image} (hc : CodeAt im (pcOf 54531) tailWords) (s : MachineState) (hpc : s.pc = pcOf 54531) :
    ∃ t, Steps im s 1 1 t ∧ t.pc = pcOf 457 ∧ RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound tailRun hc s hpc (by simp [tailRun.res, rv_simp]), ?_, ?_, ?_⟩
  · rfl
  · intro r hr; cases r <;> rfl
  · intro A _ _; simp [tailRun.res, rv_simp]

/-- KCOPY's code (a class, so the layer-recovery sections can take it as an instance like `EntryCode`). -/
class Code (im : Image) : Prop where
  head : CodeAt im (pcOf 54522) headWords
  loop : CodeAt im (pcOf 54526) loopWords
  tail : CodeAt im (pcOf 54531) tailWords

/-- KCOPY: 1,190 steps from 54522 to the counter search entry 457, copying the 237 doublewords at `0xFF9E00` to RAM
`0xA0000 .. 0xA0768`. -/
theorem kcopy_spec {im : Image} [Code im] (s : MachineState) (hpc : s.pc = pcOf 54522) :
    ∃ u, Steps im s 1190 1190 u ∧ u.pc = pcOf 457 ∧
      (∀ k, k < 237 → u.getMem (BitVec.ofNat 64 (0xA0000 + 8 * k)) = s.getMem (BitVec.ofNat 64 (0xFF9E00 + 8 * k))) ∧
      RegsExcept s u [.x6,.x28,.x29,.x30] ∧ Frame s u (fun A => 0xA0000 ≤ A ∧ A < 0xA0768) := by
  obtain ⟨t0, s0, p0, a28, a29, a30, r0, f0⟩ := head_spec (Code.head (im := im)) s hpc
  obtain ⟨t1, s1, p1, b28, b29, m1, r1, f1⟩ := loop_copy (Code.loop (im := im)) 236 t0 0xFF9E00 0xA0000
    (by decide) (by decide) (by decide) (by decide) p0 a28 a29 (by rw [a30])
  obtain ⟨u, s4, p4, r4, f4⟩ := tail_spec (Code.tail (im := im)) t1 p1
  refine ⟨u, ((s0.trans s1).trans s4).of_eq (by norm_num) (by norm_num), p4, ?_, ?_, ?_⟩
  · intro k hk
    rw [f4.get (by omega) (by simp), m1 k (by omega), f0.get (by omega) (by simp)]
  · exact ((r0.trans r1).trans r4).mono (by decide)
  · exact ((f0.trans f1).trans f4).mono (fun A _ h => by
      rcases h with ((h | h) | h) <;> first | exact h.elim | omega)

theorem installed_code : Code Images.expandImage := by
  constructor <;> (apply codeAt_t51_at <;> decide)

end SigGolfCandidate.T3M.Expand.KCopy
end
-- ==== merged from T3M_Search_DigestSearch ====
section

section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
section blocks
variable {image : Image} {b : Nat}
theorem so3_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf (b + 7) ∧ t.getReg .x21 = BitVec.ofNat 64 21 ∧
      t.getReg .x20 = BitVec.ofNat 64 0 ∧ t.getReg .x25 = BitVec.ofNat 64 SEL ∧
      RegsExcept s t [.x20, .x21, .x25] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_3 hK.2.1) (codeAt_k_3 hK) s hpc (by simp [st_3, blk354_3.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_3, blk354_3.res, E.eval]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · simp [st_3, blk354_3.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_3, blk354_3.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_3, blk354_3.res, rv_simp]
theorem so7_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 7)) (c : Nat)
    (hc : c ≤ 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if c < 7 then pcOf (b + 9) else pcOf (b + 97)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_7 hK.2.1) (codeAt_k_7 hK) s hpc (by simp [st_7, blk354_7.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_7, rebase, blk354_7.res, E.eval, CmpOp.eval, h20]
    rw [ofNat_slt c 7 (by omega) (by omega)]
    by_cases h : c < 7 <;> simp [h]
  · intro r hr; simp at hr; cases r <;> simp_all [st_7, blk354_7.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_7, blk354_7.res, rv_simp]
theorem so9_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 9))
    (c : Nat) (hc : c < 7) (h20 : s.getReg .x20 = BitVec.ofNat 64 c) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 22 22 t ∧ t.pc = pcOf (b + 31) ∧
      t.getReg .x28 = BitVec.ofNat 64 (selWin N c) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_9 hK.2.1) (codeAt_k_9 hK) s hpc ?_, ?_, ?_, ?_, ?_⟩
  · interval_cases c <;> simp [st_9, blk354_9.res, rv_simp, h20, accessValid_iff, MEMORY_BYTES]
  · simp [pcE_9, blk354_9.res, E.eval]
  · simp only [Result.toState_getReg, st_9, blk354_9.res]
    interval_cases c <;> simpa [rv_simp, h20] using window_mem s N hN _ hc
  · intro r hr; simp at hr; cases r <;> simp_all [st_9, blk354_9.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_9, blk354_9.res, rv_simp]
theorem so31_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if u / 16 % 128 ≤ u / 2 ^ 11 % 128 then pcOf (b + 43) else pcOf (b + 40)) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 (u / 16 % 128) ∧
      t.getReg .x23 = BitVec.ofNat 64 (u / 2 ^ 11 % 128) ∧
      t.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  have hu' : u < 2 ^ 64 := by omega
  refine ⟨_, symRun_sound (run_31 hK.2.1) (codeAt_k_31 hK) s hpc (by simp [st_31, blk354_31.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_31, rebase, blk354_31.res, E.eval, CmpOp.eval, h28, BinOp.eval,
      ofNat_shr _ _ hu', ofNat_and127]
    rw [ofNat_slt _ _ (by omega) (by omega)]
    by_cases h : u / 16 % 128 ≤ u / 2 ^ 11 % 128 <;> simp [h]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · simp only [Result.toState_getReg, st_31, blk354_31.res]
    t3n [h28, ofNat_shr _ _ hu', ofNat_and15, ofNat_and127]
  · intro r hr; simp at hr; cases r <;> simp_all [st_31, blk354_31.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_31, blk354_31.res, rv_simp]
theorem so40_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 40)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 43) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_40 hK.2.1) (codeAt_k_40 hK) s hpc (by simp [st_40, blk354_40.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_40, blk354_40.res, E.eval]
  · simp [st_40, blk354_40.res, rv_simp]
  · simp [st_40, blk354_40.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_40, blk354_40.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_40, blk354_40.res, rv_simp]
theorem so43_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 43)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x24 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 47) else pcOf (b + 44)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_43 hK.2.1) (codeAt_k_43 hK) s hpc (by simp [st_43, blk354_43.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_43, rebase, blk354_43.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_43, blk354_43.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_43, blk354_43.res, rv_simp]
theorem so44_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 44)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 47) ∧ t.getReg .x23 = s.getReg .x24 ∧
      t.getReg .x24 = s.getReg .x23 ∧ RegsExcept s t [.x7, .x23, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_44 hK.2.1) (codeAt_k_44 hK) s hpc (by simp [st_44, blk354_44.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_44, blk354_44.res, E.eval]
  · simp [st_44, blk354_44.res, rv_simp]
  · simp [st_44, blk354_44.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_44, blk354_44.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_44, blk354_44.res, rv_simp]
theorem so47_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 47)) (x y : Nat)
    (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) (hhi : s.getReg .x23 = BitVec.ofNat 64 x)
    (hlo : s.getReg .x22 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if y ≤ x then pcOf (b + 51) else pcOf (b + 48)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_47 hK.2.1) (codeAt_k_47 hK) s hpc (by simp [st_47, blk354_47.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_47, rebase, blk354_47.res, E.eval, CmpOp.eval, hhi, hlo]
    rw [ofNat_slt _ _ hx hy]
    by_cases h : y ≤ x
    · simp [h, show ¬ x < y by omega]
    · simp [h, show x < y by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_47, blk354_47.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_47, blk354_47.res, rv_simp]
theorem so48_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 48)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + 51) ∧ t.getReg .x22 = s.getReg .x23 ∧
      t.getReg .x23 = s.getReg .x22 ∧ RegsExcept s t [.x7, .x22, .x23] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_48 hK.2.1) (codeAt_k_48 hK) s hpc (by simp [st_48, blk354_48.res, rv_simp]),
    ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcE_48, blk354_48.res, E.eval]
  · simp [st_48, blk354_48.res, rv_simp]
  · simp [st_48, blk354_48.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_48, blk354_48.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_48, blk354_48.res, rv_simp]
theorem so51_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 51)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x22 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x23 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 52)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_51 hK.2.1) (codeAt_k_51 hK) s hpc (by simp [st_51, blk354_51.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_51, rebase, blk354_51.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_51, blk354_51.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_51, blk354_51.res, rv_simp]
theorem so52_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 52)) (x y : Nat)
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h1 : s.getReg .x23 = BitVec.ofNat 64 x)
    (h2 : s.getReg .x24 = BitVec.ofNat 64 y) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if x = y then pcOf (b + 101) else pcOf (b + 53)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_52 hK.2.1) (codeAt_k_52 hK) s hpc (by simp [st_52, blk354_52.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_52, rebase, blk354_52.res, E.eval, CmpOp.eval, h1, h2]
    by_cases h : x = y
    · simp [h]
    · simp [h, ofNat_inj hx hy]
  · intro r hr; simp at hr; cases r <;> simp_all [st_52, blk354_52.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_52, blk354_52.res, rv_simp]
theorem so53_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 53))
    (a y z R S P c : Nat) (ha : a < 256) (hy : y < 256) (hz : z < 256)
    (hP : P + 24 ≤ 2 ^ 24) (hP8 : P % 8 = 0)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 a) (h23 : s.getReg .x23 = BitVec.ofNat 64 y)
    (h24 : s.getReg .x24 = BitVec.ofNat 64 z) (h6 : s.getReg .x6 = BitVec.ofNat 64 R)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 S) (h25 : s.getReg .x25 = BitVec.ofNat 64 P)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 44 44 t ∧ t.pc = pcOf (b + 7) ∧
      t.getReg .x21 = BitVec.ofNat 64 (S + ((a ^^^ y).log2 + 1) + ((y ^^^ z).log2 + 1) + 4) ∧
      t.getMem (BitVec.ofNat 64 P) = BitVec.ofNat 64 (R + a) ∧
      t.getMem (BitVec.ofNat 64 (P + 8)) = BitVec.ofNat 64 (R + y) ∧
      t.getMem (BitVec.ofNat 64 (P + 16)) = BitVec.ofNat 64 (R + z) ∧
      t.getReg .x25 = BitVec.ofNat 64 (P + 24) ∧ t.getReg .x20 = BitVec.ofNat 64 (c + 1) ∧
      RegsExcept s t [.x7, .x20, .x21, .x25, .x28, .x29] ∧
      Frame s t (fun A => A = P ∨ A = P + 8 ∨ A = P + 16) := by
  have hay : a ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) ha hy
  have hyz : y ^^^ z < 256 := Nat.xor_lt_two_pow (n := 8) hy hz
  refine ⟨_, symRun_sound (run_53 hK.2.1) (codeAt_k_53 hK) s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st_53, blk354_53.res, rv_simp, h25, accessValid_iff, MEMORY_BYTES]; omega
  · simp [pcE_53, blk354_53.res, E.eval]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    simp only [rv_simp, h22, h23, h24, h21, ofNat_xor a y (by omega) (by omega),
      ofNat_xor y z (by omega) (by omega)]
    rw [bitlen_word _ hay, bitlen_word _ hyz]
    t3n []
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h22, h6]
    all_goals (split_ifs <;> first | omega | rfl)
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h23, h6]
    split_ifs <;> first | omega | rfl
  · simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25, h24, h6]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h25]
  · simp only [Result.toState_getReg, st_53, blk354_53.res]
    t3n [h20]
  · intro r hr; simp at hr; cases r <;> simp_all [st_53, blk354_53.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, st_53, blk354_53.res]
    t3n [h25]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem so97_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 97)) (S : Nat)
    (hS : S < 2 ^ 63) (h21 : s.getReg .x21 = BitVec.ofNat 64 S) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if 116 ≤ S then pcOf (b + 101) else pcOf (b + 99)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_97 hK.2.1) (codeAt_k_97 hK) s hpc (by simp [st_97, blk354_97.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcE_97, rebase, blk354_97.res, E.eval, CmpOp.eval, h21]
    rw [ofNat_slt _ _ hS (by omega)]
    by_cases h : 116 ≤ S
    · simp [h, show ¬ S < 116 by omega]
    · simp [h, show S < 116 by omega]
  · intro r hr; simp at hr; cases r <;> simp_all [st_97, blk354_97.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_97, blk354_97.res, rv_simp]
theorem so99_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 99)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 1 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_99 hK.2.1) (codeAt_k_99 hK) s hpc (by simp [st_99, blk354_99.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_99, blk354_99.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_99, blk354_99.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_99, blk354_99.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_99, blk354_99.res, rv_simp]
theorem so101_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 101)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf ret ∧ t.getReg .x13 = BitVec.ofNat 64 0 ∧
      RegsExcept s t [.x13] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_101 hK.2.1) (codeAt_k_101 hK) s hpc (by simp [st_101, blk354_101.res, rv_simp]),
    ?_, ?_, ?_, ?_⟩
  · simp [pcE_101, blk354_101.res, E.eval, BinOp.eval, h1, pcOf_and_not1]
  · simp [st_101, blk354_101.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [st_101, blk354_101.res, rv_simp] <;> rfl
  · intro A _ _; simp [st_101, blk354_101.res, rv_simp]
end blocks
section sort
variable {image : Image} {b : Nat}
theorem exch {rlo rhi : Reg} {o nxt : Nat}
    (hsw : ∀ s : MachineState, s.pc = pcOf (b + o) → ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = s.getReg rhi ∧ t.getReg rhi = s.getReg rlo ∧ RegsExcept s t [.x7, rlo, rhi] ∧
      Frame s t (fun _ => False))
    (s : MachineState) (x y : Nat)
    (hpc : s.pc = if x ≤ y then pcOf (b + nxt) else pcOf (b + o))
    (hlo : s.getReg rlo = BitVec.ofNat 64 x) (hhi : s.getReg rhi = BitVec.ofNat 64 y) :
    ∃ k t, Steps image s k k t ∧ k ≤ 3 ∧ t.pc = pcOf (b + nxt) ∧
      t.getReg rlo = BitVec.ofNat 64 (min x y) ∧ t.getReg rhi = BitVec.ofNat 64 (max x y) ∧
      RegsExcept s t [.x7, rlo, rhi] ∧ Frame s t (fun _ => False) := by
  by_cases h : x ≤ y
  · rw [if_pos h] at hpc
    refine ⟨0, s, Steps.refl s, by omega, hpc, ?_, ?_, RegsExcept.refl _ _, Frame.refl _ _⟩
    · rw [hlo, Nat.min_eq_left h]
    · rw [hhi, Nat.max_eq_right h]
  · rw [if_neg h] at hpc
    obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := hsw s hpc
    refine ⟨3, t, h1, le_refl _, h2, ?_, ?_, h5, h6⟩
    · rw [h3, hhi, Nat.min_eq_right (by omega)]
    · rw [h4, hlo, Nat.max_eq_left (by omega)]
theorem sort_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 31))
    (u : Nat) (hu : u < 2 ^ 25) (h28 : s.getReg .x28 = BitVec.ofNat 64 u) :
    ∃ k t, Steps image s k k t ∧ k ≤ 20 ∧ t.pc = pcOf (b + 51) ∧
      t.getReg .x6 = BitVec.ofNat 64 (u % 16 * 128) ∧
      t.getReg .x22 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 0 0) ∧
      t.getReg .x23 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 1 0) ∧
      t.getReg .x24 = BitVec.ofNat 64 ((sort3 (u / 16 % 128) (u / 2 ^ 11 % 128) (u / 2 ^ 18 % 128)).getD 2 0) ∧
      RegsExcept s t [.x6, .x22, .x23, .x24, .x7] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, h6, h22, h23, h24, r1, f1⟩ := so31_spec hK s hpc u hu h28
  obtain ⟨k2, t2, s2, k2le, p2, a22, a23, r2, f2⟩ :=
    exch (so40_spec hK) t1 _ _ p1 h22 h23
  have b24 : t2.getReg .x24 = BitVec.ofNat 64 (u / 2 ^ 18 % 128) := by
    rw [r2.get (by decide), h24]
  obtain ⟨t3, s3, p3, r3, f3⟩ := so43_spec hK t2 p2 _ _ (by omega) (by omega) b24 a23
  obtain ⟨k4, t4, s4, k4le, p4, a23', a24, r4, f4⟩ :=
    exch (so44_spec hK) t3 (max (u / 16 % 128) (u / 2 ^ 11 % 128))
      (u / 2 ^ 18 % 128) p3 (by rw [r3.get (by decide), a23]) (by rw [r3.get (by decide), b24])
  have b22 : t4.getReg .x22 = BitVec.ofNat 64 (min (u / 16 % 128) (u / 2 ^ 11 % 128)) := by
    rw [r4.get (by decide), r3.get (by decide), a22]
  obtain ⟨t5, s5, p5, r5, f5⟩ := so47_spec hK t4 p4 _ _ (by omega) (by omega) a23' b22
  obtain ⟨k6, t6, s6, k6le, p6, a22', a23'', r6, f6⟩ :=
    exch (so48_spec hK) t5 _ _ p5
      (by rw [r5.get (by decide), b22]) (by rw [r5.get (by decide), a23'])
  refine ⟨9 + k2 + 1 + k4 + 1 + k6, t6, ?_, by omega, p6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6
    exact this
  · rw [r6.get (by decide), r5.get (by decide), r4.get (by decide), r3.get (by decide),
      r2.get (by decide), h6]
  · rw [a22']; rfl
  · rw [a23'']; rfl
  · rw [r6.get (by decide), r5.get (by decide), a24]; rfl
  · exact ((((((r1.trans r2).trans r3).trans r4).trans r5).trans r6).mono (by decide))
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).mono (by simp)
end sort
def RowAt (t : MachineState) (N : BitVec 256) (c : Nat) : Prop :=
  ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) =
    BitVec.ofNat 64 (selBucket N c * 128 + (selRow N c).getD j 0)
def SelW (A : Nat) : Prop := SEL ≤ A ∧ A < SEL + 168
abbrev selRegs : List Reg := [.x6, .x7, .x13, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29]
theorem NAt.frame {s t : MachineState} {N : BitVec 256} (h : NAt s N) (hf : Frame s t SelW) : NAt t N := by
  intro j hj
  rw [hf.get (by simp only [NBUF]; omega) (by simp only [SelW, SEL, NBUF]; omega)]
  exact h j hj
section loop
variable {image : Image} {b : Nat}
structure SelInv (b : Nat) (s0 : MachineState) (N : BitVec 256) (c : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (b + 7)
  x20 : t.getReg .x20 = BitVec.ofNat 64 c
  x21 : t.getReg .x21 = BitVec.ofNat 64 (21 + selCost N c)
  x25 : t.getReg .x25 = BitVec.ofNat 64 (SEL + 24 * c)
  ok : ∀ c' < c, rowOk (selRow N c') = true
  rows : ∀ c' < c, RowAt t N c'
  regs : RegsExcept s0 t selRegs
  frame : Frame s0 t SelW
macro "sel_frame" : tactic =>
  `(tactic| (intro A _ hA; (try simp only [or_false, false_or, or_self] at hA); first | exact hA | (simp only [SelW, SEL] at *; omega)))
theorem regs_mono {s t : MachineState} {l : List Reg} (h : RegsExcept s t l)
    (hl : l.all (fun r => decide (r ∈ selRegs)) = true) : RegsExcept s t selRegs :=
  h.mono (fun r hr => by simpa using List.all_eq_true.1 hl r hr)
theorem sel_body (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) {c : Nat}
    (hc : c < 7) {t : MachineState} (hI : SelInv b s0 N c t) :
    ∃ k u, Steps image t k k u ∧ k ≤ 90 ∧
      (if rowOk (selRow N c) then SelInv b s0 N (c + 1) u
       else u.pc = pcOf (b + 101) ∧ RegsExcept s0 u selRegs ∧ Frame s0 u SelW) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := so7_spec hK t hI.pc c (by omega) hI.x20
  rw [if_pos hc] at p1
  have hN1 : NAt t1 N := (hN.frame hI.frame).frame (f1.mono (by simp))
  obtain ⟨t2, s2, p2, h28, r2, f2⟩ := so9_spec hK t1 p1 c hc (by rw [r1.get (by decide), hI.x20]) N hN1
  obtain ⟨k3, t3, s3, k3le, p3, h6, h22, h23, h24, r3, f3⟩ := sort_spec hK t2 p2 _ (selWin_lt N c) h28
  have hrow : ∀ j, (selRow N c).getD j 0 < 128 := selRow_lt N c
  have g22 : t3.getReg .x22 = BitVec.ofNat 64 ((selRow N c).getD 0 0) := h22
  have g23 : t3.getReg .x23 = BitVec.ofNat 64 ((selRow N c).getD 1 0) := h23
  have g24 : t3.getReg .x24 = BitVec.ofNat 64 ((selRow N c).getD 2 0) := h24
  obtain ⟨t4, s4, p4, r4, f4⟩ := so51_spec hK t3 p3 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) (by have := hrow 0; omega)
    (by have := hrow 1; omega) g22 g23
  have regs4 : RegsExcept s0 t4 selRegs :=
    regs_mono ((((hI.regs.trans r1).trans r2).trans r3).trans r4) (by decide)
  have frame4 : Frame s0 t4 SelW := ((((hI.frame.trans f1).trans f2).trans f3).trans f4).mono
    (by sel_frame)
  by_cases e1 : (selRow N c).getD 0 0 = (selRow N c).getD 1 0
  · rw [if_pos e1] at p4
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e1]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    refine ⟨2 + 22 + k3 + 1, t4, ((s1.trans s2).trans s3).trans s4, by omega, ?_⟩
    rw [hok]; exact ⟨p4, regs4, frame4⟩
  rw [if_neg e1] at p4
  obtain ⟨t5, s5, p5, r5, f5⟩ := so52_spec hK t4 p4 ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (by have := hrow 1; omega)
    (by have := hrow 2; omega) (by rw [r4.get (by decide), g23]) (by rw [r4.get (by decide), g24])
  by_cases e2 : (selRow N c).getD 1 0 = (selRow N c).getD 2 0
  · rw [if_pos e2] at p5
    have hok : rowOk (selRow N c) = false := by
      rw [rowOk, e2]; simp only [ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    refine ⟨2 + 22 + k3 + 1 + 1, t5, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, ?_⟩
    rw [hok]
    exact ⟨p5, regs_mono (regs4.trans r5) (by decide),
      (frame4.trans f5).mono (by sel_frame)⟩
  rw [if_neg e2] at p5
  have hok : rowOk (selRow N c) = true := by
    rw [rowOk]; simp only [ne_eq, e1, e2, not_false_eq_true, decide_true, Bool.and_self]
  have hcost := selCost_le N c
  obtain ⟨t6, s6, p6, h21', m0, m8, m16, h25', h20', r6, f6⟩ :=
    so53_spec hK t5 p5 ((selRow N c).getD 0 0) ((selRow N c).getD 1 0) ((selRow N c).getD 2 0) (selBucket N c * 128) (21 + selCost N c) (SEL + 24 * c) c (by have := hrow 0; omega) (by have := hrow 1; omega) (by have := hrow 2; omega)
      (by simp only [SEL]; omega) (by simp only [SEL]; omega)
      (by rw [r5.get (by decide), r4.get (by decide), g22])
      (by rw [r5.get (by decide), r4.get (by decide), g23])
      (by rw [r5.get (by decide), r4.get (by decide), g24])
      (by rw [r5.get (by decide), r4.get (by decide), h6]; rfl)
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x21])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x25])
      (by rw [r5.get (by decide), r4.get (by decide), r3.get (by decide), r2.get (by decide),
            r1.get (by decide), hI.x20])
  refine ⟨2 + 22 + k3 + 1 + 1 + 44, t6, ((((s1.trans s2).trans s3).trans s4).trans s5).trans s6,
    by omega, ?_⟩
  rw [if_pos hok]
  have fr0 := (((((f1.trans f2).trans f3).trans f4).trans f5).trans f6)
  have fr : Frame t t6 SelW := fr0.mono (by sel_frame)
  refine ⟨p6, h20', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h21', selCost_succ]; unfold rowCost; congr 1; omega
  · rw [h25']; congr 1
  · intro c' hc'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · exact hI.ok c' h
    · exact hok
  · intro c' hc' j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hc' with h | rfl
    · rw [fr0.get (by simp only [SEL]; omega) (by simp only [SEL, or_false, false_or]; omega)]
      exact hI.rows c' h j hj
    · interval_cases j
      · simpa [selBucket, Nat.add_comm] using m0
      · simpa [selBucket, Nat.add_comm] using m8
      · simpa [selBucket, Nat.add_comm] using m16
  · exact regs_mono (regs4.trans (r5.trans r6)) (by decide)
  · exact (hI.frame.trans fr).mono (by intro A _ hA; rcases hA with hA | hA <;> exact hA)
theorem sel_loop (hK : KernAt image b) {s0 : MachineState} {N : BitVec 256} (hN : NAt s0 N) :
    ∀ n c t, c + n = 7 → SelInv b s0 N c t →
      ∃ k u, Steps image t k k u ∧ k ≤ 90 * n ∧
        ((u.pc = pcOf (b + 101) ∧ (List.range 7).all (fun c => rowOk (selRow N c)) = false ∧
          RegsExcept s0 u selRegs ∧ Frame s0 u SelW) ∨ SelInv b s0 N 7 u) := by
  intro n
  induction n with
  | zero => intro c t hc hI; exact ⟨0, t, Steps.refl t, le_refl _, Or.inr (by simpa using hc ▸ hI)⟩
  | succ n ih =>
    intro c t hc hI
    obtain ⟨k1, t1, s1, k1le, h1⟩ := sel_body hK hN (by omega) hI
    by_cases hok : rowOk (selRow N c) = true
    · rw [if_pos hok] at h1
      obtain ⟨k2, t2, s2, k2le, h2⟩ := ih (c + 1) t1 (by omega) h1
      exact ⟨k1 + k2, t2, s1.trans s2, by rw [Nat.mul_succ]; omega, h2⟩
    · rw [if_neg hok] at h1
      refine ⟨k1, t1, s1, by rw [Nat.mul_succ]; omega, Or.inl ⟨h1.1, ?_, h1.2⟩⟩
      rw [List.all_eq_false]
      exact ⟨c, List.mem_range.2 (by omega), hok⟩
theorem selectOk_spec (hK : KernAt image b) (s : MachineState) (hpc : s.pc = pcOf (b + 3)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 640 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.admissible (T3.selections N) then 1 else 0) ∧
      (T3.admissible (T3.selections N) = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨t0, s0', p0, h21, h20, h25, r0, f0⟩ := so3_spec hK s hpc
  have hI : SelInv b s N 0 t0 :=
    ⟨p0, h20, by simpa [selCost_zero] using h21, by simpa using h25, fun _ h => absurd h (by omega),
      fun _ h => absurd h (by omega), regs_mono r0 (by decide), f0.mono (by intro _ _ h; exact h.elim)⟩
  obtain ⟨k1, t1, s1, k1le, h⟩ := sel_loop hK hN 7 0 t0 rfl hI
  have hx1 : ∀ u, RegsExcept s u selRegs → u.getReg .x1 = pcOf ret := fun u hu => by
    rw [hu.get (by decide), h1]
  rcases h with ⟨p1, hall, r1, f1⟩ | hI7
  · obtain ⟨t2, s2, p2, h13, r2, f2⟩ := so101_spec hK t1 p1 ret (hx1 t1 r1)
    have hadm : T3.admissible (T3.selections N) = false := by
      rw [admissible_selections, hall, Bool.false_and]
    refine ⟨4 + k1 + 2, t2, (s0'.trans s1).trans s2, by omega, p2, by rw [h13, hadm]; rfl,
      fun h => by rw [hadm] at h; exact absurd h (by decide), regs_mono (r1.trans r2) (by decide),
      f1.trans f2 |>.mono (by intro A _ hA; rcases hA with hA | hA; exact hA; exact hA.elim)⟩
  · have hS := selCost_le N 7
    obtain ⟨t2, s2, p2, r2, f2⟩ := so7_spec hK t1 hI7.pc 7 (le_refl _) hI7.x20
    rw [if_neg (by omega)] at p2
    obtain ⟨t3, s3, p3, r3, f3⟩ := so97_spec hK t2 p2 (21 + selCost N 7) (by omega)
      (by rw [r2.get (by decide), hI7.x21])
    have hall : (List.range 7).all (fun c => rowOk (selRow N c)) = true :=
      List.all_eq_true.2 (fun c hc => hI7.ok c (List.mem_range.1 hc))
    have rr : RegsExcept s t3 selRegs := regs_mono ((hI7.regs.trans r2).trans r3) (by decide)
    have ff : Frame t1 t3 (fun _ => False) := (f2.trans f3).mono (by intro A _ hA; simpa using hA)
    by_cases hc : 116 ≤ 21 + selCost N 7
    · rw [if_pos hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so101_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = false := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun h => by rw [hadm] at h; exact absurd h (by decide),
        regs_mono (rr.trans r4) (by decide), ?_⟩
      exact ((hI7.frame.trans ff).trans f4).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)
    · rw [if_neg hc] at p3
      obtain ⟨t4, s4, p4, h13, r4, f4⟩ := so99_spec hK t3 p3 ret (hx1 t3 rr)
      have hadm : T3.admissible (T3.selections N) = true := by
        rw [admissible_selections, hall, Bool.true_and]; simp; omega
      have fr : Frame t1 t4 (fun _ => False) := (ff.trans f4).mono (by intro A _ hA; simpa using hA)
      refine ⟨4 + k1 + 2 + 2 + 2, t4, (((s0'.trans s1).trans s2).trans s3).trans s4, by omega, p4,
        by rw [h13, hadm]; rfl, fun _ c hc j hj => ?_, regs_mono (rr.trans r4) (by decide),
        (hI7.frame.trans fr).mono (by intro A _ hA; simp only [or_false] at hA; exact hA)⟩
      rw [fr.get (by simp only [SEL]; omega) (by simp)]
      exact hI7.rows c hc j hj
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gate_word (N : BitVec 256) :
    N.extractLsb' 192 64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_ofNat, show (7 : Nat) = 2 ^ 3 - 1 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases h : i < 3
  · simp [h, hi, show 14 + i < 64 by omega, BitVec.testBit_toNat,
      show 192 + (14 + i) = i + 206 by omega]
  · simp [h]
theorem gate_head_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (N : BitVec 256) (hN : NAt s N) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if N.toNat / 2 ^ 206 % 8 = 0 then pcOf (gatePc b + 5) else pcOf (b + 101)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gate hK.2.1) (codeAt_gateHead hG) s hpc
    (by simp [gateSt, blkGateE.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_⟩
  · have hw := hN 3 (by decide)
    have hh : s.getMem 131448#64 >>> 14 &&& 7#64 = BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) := by
      simpa only [NBUF] using hw ▸ gate_word N
    simp only [Result.toState_pc, gateEnd, rebase, blkGateE.res, E.eval, BinOp.eval, CmpOp.eval]
    change (if (s.getMem 131448#64 >>> 14 &&& 7#64 != 0#64) = true then pcOf (b + 101) else pcOf (gatePc b + 5)) = _
    rw [hh]
    have he : (BitVec.ofNat 64 (N.toNat / 2 ^ 206 % 8) = 0#64) ↔ N.toNat / 2 ^ 206 % 8 = 0 :=
      ofNat_inj (by have := Nat.mod_lt (N.toNat / 2 ^ 206) (show 0 < 8 by decide); omega) (by decide)
    simp only [bne_iff_ne, ne_eq, he, ite_not]
  · intro r hr; simp at hr; cases r <;> simp_all [gateSt, blkGateE.res, rv_simp] <;> rfl
  · intro A _ _; simp [gateSt, blkGateE.res, rv_simp]
theorem gate_jump_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 3) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gateJump hK.2.1) (codeAt_gateJump hG) s hpc
    (by simp [blkGateJE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [E.eval]
  · intro r hr; cases r <;> simp [blkGateJE.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGateJE.res, rv_simp]
theorem gatedSelect_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b)) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) (N : BitVec 256) (hN : NAt s N) :
    ∃ k t, Steps image s k k t ∧ k ≤ 646 ∧ t.pc = pcOf ret ∧
      t.getReg .x13 = BitVec.ofNat 64 (if T3.digestAdmissible N then 1 else 0) ∧
      (T3.digestAdmissible N = true → ∀ c < 7, RowAt t N c) ∧
      RegsExcept s t selRegs ∧ Frame s t SelW := by
  obtain ⟨u, hs, hp, hr, hf⟩ := gate_head_spec hK hG s hpc N hN
  have hN' : NAt u N := by intro j hj; rw [hf.get (by simp only [NBUF]; omega) (by simp)]; exact hN j hj
  have hu1 : u.getReg .x1 = pcOf ret := by rw [hr.get (by decide), h1]
  by_cases hg : N.toNat / 2 ^ 206 % 8 = 0
  · rw [if_pos hg] at hp
    obtain ⟨v, hs', hp', hr', hf'⟩ := gate_jump_spec hK hG u hp
    have hN'' : NAt v N := by intro j hj; rw [hf'.get (by simp only [NBUF]; omega) (by simp)]; exact hN' j hj
    have hv1 : v.getReg .x1 = pcOf ret := by rw [hr'.get (by decide), hu1]
    obtain ⟨k, t, st, hk, pt, ht13, htrows, rt, ft⟩ := selectOk_spec hK v hp' ret hv1 N hN''
    have hgB : T3.digestGate N = true := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = true; exact decide_eq_true hg
    have he : T3.digestAdmissible N = T3.admissible (T3.selections N) := by simp only [T3.digestAdmissible, hgB, Bool.and_true]
    refine ⟨5 + 1 + k, t, (hs.trans hs').trans st, by omega, pt, by simpa [he] using ht13,
      by simpa [he] using htrows, ?_, ?_⟩
    · exact regs_mono ((hr.trans hr').trans rt) (by decide)
    · exact ((hf.trans hf').trans ft).mono (by intro A _ h; simpa using h)
  · rw [if_neg hg] at hp
    obtain ⟨t, st, pt, ht13, rt, ft⟩ := so101_spec hK u hp ret hu1
    have hgB : T3.digestGate N = false := by change decide (N.toNat / 2 ^ 206 % 8 = 0) = false; exact decide_eq_false hg
    have he : T3.digestAdmissible N = false := by simp only [T3.digestAdmissible, hgB, Bool.and_false]
    refine ⟨7, t, hs.trans st, by decide, pt, by simpa [he] using ht13,
      by simp [he], ?_, ?_⟩
    · exact regs_mono (hr.trans rt) (by decide)
    · exact (hf.trans ft).mono (by intro A _ h; simpa using h)
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3 (Digest Layer HashOutput)
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 8192
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
theorem digestInput_length (rho : Digest) (m : T3.Message) (c : BitVec 32) : (T3.digestInput rho m c).length = 64 := by
  simp only [T3.digestInput, List.length_append, SphincsSecurity.bytesLE_length]
theorem pad64_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    T3.pad64 (T3.digestInput rho m c) = T3.digestInput rho m c := by
  unfold T3.pad64
  rw [digestInput_length]
  simp
theorem wordsOf_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    wordsOf (T3.pad64 (T3.digestInput rho m c)) =
      [rho.extractLsb' 0 64, rho.extractLsb' 64 64, BitVec.ofNat 64 0,
        BitVec.ofNat 64 c.toNat, m.extractLsb' 0 64, m.extractLsb' 64 64, m.extractLsb' 128 64,
        m.extractLsb' 192 64] := by
  rw [pad64_digestInput]
  unfold T3.digestInput
  rw [wordsOf_append _ _ (by simp only [List.length_append, SphincsSecurity.bytesLE_length]),
    wordsOf_append _ _ (by simp only [SphincsSecurity.bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16,
    wordsOf_bytesLE32, T3.digestHeader_low, T3.digestHeader_high]
  rfl
theorem blocks_digestInput (rho : Digest) (m : T3.Message) (c : BitVec 32) :
    (toQ (T3.pad64 (T3.digestInput rho m c))).blocks = 1 := by
  rw [pad64_digestInput, blocks_toQ (by rw [Aligned, digestInput_length]; omega), digestInput_length]
theorem TBSim.publicHash_bind {β : Type} {image : Image} {sk : BitVec 256} {s : MachineState}
    {input : List UInt8} {W : Nat} {f : HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
section blocks
variable {image : Image} {d b : Nat}
theorem ds0_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 0)) (i : Nat)
    (hi : i ≤ 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i = 2 ^ 20 then pcOf (b + 0) else pcOf (d + 2)) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds0 hD.2) (codeAt_ds_0 hD) s hpc (by simp [stds_0, blkds30_0.res, rv_simp]),
    ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_0, rebase, blkds30_0.res, E.eval, CmpOp.eval, h19]
    by_cases h : i = 2 ^ 20
    · subst h; simp
    · have : (BitVec.ofNat 64 i == 1048576#64) = false := by
        rw [beq_eq_false_iff_ne, ne_eq, ofNat_eq_iff]; omega
      rw [this, if_neg (by simp), if_neg h]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_0, blkds30_0.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_0, blkds30_0.res, rv_simp]
theorem ds2_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 2)) (i : Nat)
    (hi : i < 2 ^ 20) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 12 12 t ∧ t.pc = pcOf (d + 14) ∧
      t.getMem (BitVec.ofNat 64 (DIG + 16)) = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (DIG + 24)) = BitVec.ofNat 64 i ∧
      t.getReg .x10 = BitVec.ofNat 64 DIG ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NBUF ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28] ∧ Frame s t (fun A => A = DIG + 16 ∨ A = DIG + 24) := by
  refine ⟨_, symRun_sound (run_ds2 hD.2) (codeAt_ds_2 hD) s hpc
    (by simp [stds_2, blkds30_2.res, rv_simp, accessValid_iff, MEMORY_BYTES]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pcEds_2, E.eval]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [DIG]
  · simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n [h19, DIG]
    rw [Nat.mul_one]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · simp [stds_2, blkds30_2.res, rv_simp]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_2, blkds30_2.res, rv_simp] <;> rfl
  · intro A hA hn
    simp only [Result.toState_getMem, stds_2, blkds30_2.res]
    t3n []
    simp only [DIG] at hn
    rw [if_neg (by omega), if_neg (by omega)]
theorem ds14_fetch (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 14)) :
    fetch image s = some (.base .ECALL) :=
  ((codeAt_ds_14 hD).fetch s hpc).trans rfl
theorem ds15_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 15)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (gatePc b) ∧ t.getReg .x1 = pcOf (d + 16) ∧
      RegsExcept s t [.x1] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds15 hD.2) (codeAt_ds_15 hD) s hpc
    (by simp [stds_15, blkds30_15.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_15, E.eval]
  · simp [stds_15, blkds30_15.res, rv_simp, RegFile.set]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_15, blkds30_15.res, rv_simp, RegFile.set] <;> rfl
  · intro A _ _; simp [stds_15, blkds30_15.res, rv_simp]
theorem ds16_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 16)) (ok : Bool)
    (h13 : s.getReg .x13 = BitVec.ofNat 64 (if ok then 1 else 0)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if ok then pcOf (d + 19) else pcOf (d + 17)) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds16 hD.2) (codeAt_ds_16 hD) s hpc
    (by simp [stds_16, blkds30_16.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, pcEds_16, rebase, blkds30_16.res, E.eval, CmpOp.eval, h13]
    cases ok <;> simp
  · intro r hr; simp at hr; cases r <;> simp_all [stds_16, blkds30_16.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_16, blkds30_16.res, rv_simp]
theorem ds17_spec (hD : DsAt image d b) (s : MachineState) (hpc : s.pc = pcOf (d + 17)) (i : Nat)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf (d + 0) ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      RegsExcept s t [.x19] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_ds17 hD.2) (codeAt_ds_17 hD) s hpc
    (by simp [stds_17, blkds30_17.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [pcEds_17, E.eval]
  · simp only [Result.toState_getReg, stds_17, blkds30_17.res]
    t3n [h19]
  · intro r hr; simp at hr; cases r <;> simp_all [stds_17, blkds30_17.res, rv_simp] <;> rfl
  · intro A _ _; simp [stds_17, blkds30_17.res, rv_simp]
end blocks
abbrev dsRegs : List Reg :=
  [.x1, .x6, .x7, .x10, .x11, .x12, .x13, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x28, .x29, .x30]
def DsW (X : Nat) : Prop :=
  X = DIG + 16 ∨ X = DIG + 24 ∨ (NBUF ≤ X ∧ X < NBUF + 32) ∨ (SEL ≤ X ∧ X < SEL + 168)
structure DsPre (d : Nat) (s : MachineState) (rho : Digest) (m : T3.Message) : Prop where
  pc : s.pc = pcOf d
  x5 : s.getReg .x5 = 0
  x19 : s.getReg .x19 = BitVec.ofNat 64 0
  rho : DigAt s DIG rho
  msg : ∀ k < 4, s.getMem (BitVec.ofNat 64 (DIG + 32 + 8 * k)) = m.extractLsb' (64 * k) 64
def selEntry (N : HashOutput) (c j : Nat) : Nat :=
  ((T3.selections N).getD c ⟨0, []⟩).bucket * 128 + ((T3.selections N).getD c ⟨0, []⟩).leaves.getD j 0
def SelRows (t : MachineState) (N : HashOutput) : Prop :=
  ∀ c < 7, ∀ j < 3, t.getMem (BitVec.ofNat 64 (SEL + 24 * c + 8 * j)) = BitVec.ofNat 64 (selEntry N c j)
def OutAt (t : MachineState) (A : Nat) (N : BitVec 256) : Prop :=
  ∀ k < 4, t.getMem (BitVec.ofNat 64 (A + 8 * k)) = N.extractLsb' (64 * k) 64
def DsPost (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (c, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW ∧
      c.toNat < 2 ^ 20 ∧ t.getReg .x19 = BitVec.ofNat 64 c.toNat
def DsPostS (b d : Nat) (s : MachineState) : Option (BitVec 32 × HashOutput) → MachineState → Prop
  | none, t => FailedAt b t
  | some (_, N), t => t.pc = pcOf (d + 19) ∧ t.getReg .x5 = 0 ∧ T3.admissible (T3.selections N) = true ∧
      OutAt t NBUF N ∧ SelRows t N ∧ RegsExcept s t dsRegs ∧ Frame s t DsW
def dsCostS : Nat := T3.attemptLimit * 700 + 100
theorem selEntry_eq (N : HashOutput) (c j : Nat) (hc : c < 7) :
    selEntry N c j = selBucket N c * 128 + (selRow N c).getD j 0 := by
  simp [selEntry, selections_eq, List.getD_eq_getElem?_getD, hc]
theorem NAt.writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    NAt (writeHash t a) a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
structure DsInv (d : Nat) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf (d + 0)
  hi : i ≤ 2 ^ 20
  x19 : t.getReg .x19 = BitVec.ofNat 64 i
  regs : RegsExcept s0 t dsRegs
  frame : Frame s0 t DsW
theorem ds_loop (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    ∀ F i t, i + F = 2 ^ 20 → DsInv d s0 i t →
      TBSim image sk t (F * 672 + 670) (T3.digestSearch rho m i F) (DsPost b d s0) := by
  intro F
  induction F with
  | zero =>
    intro i t h hI
    obtain ⟨t1, s1, p1, _, _⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_pos (by omega)] at p1
    obtain ⟨t2, s2, p2, h5, h10, _⟩ := cs0_spec hK t1 p1
    have := TBSim.steps (sk := sk) (s1.trans s2)
      (TBSim.pure (Q := DsPost b d s0) (a := none) ⟨p2, h5, h10⟩)
    exact this.mono (by omega) (fun _ _ h => h)
  | succ F ih =>
    intro i t h hI
    have hi : i < 2 ^ 20 := by omega
    have hc : (BitVec.ofNat 32 i).toNat = i := by rw [BitVec.toNat_ofNat]; omega
    obtain ⟨t1, s1, p1, r1, f1⟩ := ds0_spec hD t hI.pc i hI.hi hI.x19
    rw [if_neg (by omega)] at p1
    obtain ⟨u, s2, p2, h16, h24, h10, h11, h12, r2, f2⟩ :=
      ds2_spec hD t1 p1 i hi (by rw [r1.get (by decide), hI.x19])
    have ru : RegsExcept s0 u dsRegs := ((hI.regs.trans r1).trans r2).mono (by decide)
    have u19 : u.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), r1.get (by decide), hI.x19]
    have fu : Frame s0 u DsW := ((hI.frame.trans f1).trans f2).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with h | h
      · exact h
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
    have mem : ∀ A, A < 2 ^ 64 → ¬ DsW A → u.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A) :=
      fun A hA hn => fu.get hA hn
    have nw : ∀ A, A = DIG ∨ A = DIG + 8 ∨ A = DIG + 32 ∨ A = DIG + 40 ∨ A = DIG + 48 ∨ A = DIG + 56 →
        ¬ DsW A := by
      intro A hA; simp only [DsW, DIG, NBUF, SEL] at hA ⊢; omega
    have hm0 : s0.getMem (BitVec.ofNat 64 (DIG + 32)) = m.extractLsb' 0 64 := hpre.msg 0 (by decide)
    have hm1 : s0.getMem (BitVec.ofNat 64 (DIG + 40)) = m.extractLsb' 64 64 := hpre.msg 1 (by decide)
    have hm2 : s0.getMem (BitVec.ofNat 64 (DIG + 48)) = m.extractLsb' 128 64 := hpre.msg 2 (by decide)
    have hm3 : s0.getMem (BitVec.ofNat 64 (DIG + 56)) = m.extractLsb' 192 64 := hpre.msg 3 (by decide)
    have hq : hashInput u = toQ (T3.pad64 (T3.digestInput rho m (BitVec.ofNat 32 i))) := by
      refine hashInput_toQ u _ 0 DIG (by rw [pad64_digestInput, digestInput_length]) h10 (by decide) (by decide)
        h11 (by decide) ?_
      rw [readWords_eight, wordsOf_digestInput, hc, h16, h24,
        mem DIG (by decide) (nw _ (by omega)), mem (DIG + 8) (by decide) (nw _ (by omega)),
        mem (DIG + 32) (by decide) (nw _ (by omega)), mem (DIG + 40) (by decide) (nw _ (by omega)),
        mem (DIG + 48) (by decide) (nw _ (by omega)), mem (DIG + 56) (by decide) (nw _ (by omega)),
        hpre.rho.1, hpre.rho.2, hm0, hm1, hm2, hm3]
    have hv : hashArgumentsValid u = true :=
      hashArgs_const u DIG 64 NBUF h10 h11 h12 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h5 : u.getReg .x5 = 0 := by rw [ru.get (by decide), hpre.x5]
    have prog : T3.digestSearch rho m i (F + 1) =
        (T3.publicHash (T3.digestInput rho m (BitVec.ofNat 32 i)) >>= fun output =>
          if T3.digestAdmissible output then pure (some (BitVec.ofNat 32 i, output))
          else T3.digestSearch rho m (i + 1) F) := rfl
    rw [prog]
    refine (TBSim.steps (s1.trans s2) (TBSim.publicHash_bind (ds14_fetch hD u p2) h5 hv hq
      (W := 650 + (F * 672 + 670)) (fun a => ?_))).mono ?_ (fun _ _ h => h)
    swap
    · rw [blocks_digestInput]; ring_nf; omega
    have pw : (writeHash u a).pc = pcOf (d + 15) := by rw [pc_writeHash, p2, pcOf_add4]
    have hN : NAt (writeHash u a) a := NAt.writeHash u a h12
    have fw := Frame.writeHash u a NBUF h12 (by decide)
    obtain ⟨t15, s15, p15, h1, r15, f15⟩ := ds15_spec hD (writeHash u a) pw
    obtain ⟨k, t16, s16, hk, p16, h13, hrows, r16, f16⟩ := gatedSelect_spec hK hD.1.2 t15 p15 (d + 16) h1 a
      (NAt.frame hN (f15.mono (fun _ _ h => h.elim)))
    obtain ⟨t17, s17, p17, r17, f17⟩ := ds16_spec hD t16 p16 _ h13
    have r17' : RegsExcept s0 t17 dsRegs :=
      ((((ru.trans (fun r _ => getReg_writeHash u a r : RegsExcept u (writeHash u a) [])).trans r15).trans
        r16).trans r17).mono (by decide)
    have x19' : t17.getReg .x19 = BitVec.ofNat 64 i := by
      rw [r17.get (by decide), r16.get (by decide), r15.get (by decide), getReg_writeHash, u19]
    have f17' : Frame s0 t17 DsW := ((((fu.trans fw).trans f15).trans f16).trans f17).mono (fun A _ h => by
      simp only [or_false] at h
      rcases h with (h | h) | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h)))
    have hN17 : NAt t17 a :=
      NAt.frame (NAt.frame (NAt.frame hN (f15.mono (fun _ _ h => h.elim))) f16) (f17.mono (fun _ _ h => h.elim))
    by_cases hadm : T3.digestAdmissible a = true
    · simp only [hadm, ↓reduceIte] at p17 ⊢
      refine (TBSim.steps (s15.trans (s16.trans s17)) (TBSim.pure ?_)).mono (by omega) (fun _ _ h => h)
      refine ⟨p17, by rw [r17'.get (by decide), hpre.x5], (by have hh := hadm; simp only [T3.digestAdmissible, Bool.and_eq_true] at hh; exact hh.1), hN17, ?_, r17', f17', by rw [hc]; exact hi,
        by rw [hc, x19']⟩
      intro c hc7 j hj
      rw [f17.get (by simp only [SEL]; omega) (fun h => h), hrows hadm c hc7 j hj, selEntry_eq a c j hc7]
    · have hadm' : T3.digestAdmissible a = false := by simpa using hadm
      simp only [hadm', Bool.false_eq_true, ↓reduceIte] at p17 ⊢
      obtain ⟨t18, s18, p18, h19, r18, f18⟩ := ds17_spec hD t17 p17 i x19'
      have hI' : DsInv d s0 (i + 1) t18 :=
        ⟨p18, by omega, h19, (r17'.trans r18).mono (by decide),
          (f17'.trans f18).mono (fun A _ h => by simp only [or_false] at h; exact h)⟩
      refine (TBSim.steps (s15.trans (s16.trans (s17.trans s18))) (ih (i + 1) t18 (by omega) hI')).mono
        (by omega) (fun _ _ h => h)
theorem digestSearch_tbsim (hD : DsAt image d b) (hK : KernAt image b) {s0 : MachineState} {rho : Digest}
    {m : T3.Message} (hpre : DsPre d s0 rho m) :
    TBSim image sk s0 (2 ^ 20 * 672 + 670) (T3.digestSearch rho m 0 T3.attemptLimit) (DsPost b d s0) :=
  ds_loop hD hK hpre (2 ^ 20) 0 s0 (by norm_num)
    ⟨hpre.pc, by norm_num, hpre.x19, RegsExcept.refl _ _, Frame.refl _ _⟩
theorem digestSearch_spec (hD : DsAt image d b) (hK : KernAt image b) (s : MachineState) (rho : Digest)
    (m : T3.Message) (h : DsPre d s rho m) :
    TBSim image sk s dsCostS (T3.digestSearch rho m 0 T3.attemptLimit) (DsPostS b d s) := by
  refine (digestSearch_tbsim (sk := sk) hD hK h).mono (by unfold dsCostS T3.attemptLimit; omega)
    (fun r t ht => ?_)
  rcases r with _ | ⟨c, N⟩
  · exact ht
  · exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2.1, ht.2.2.2.2.2.2.1⟩
end loop
end SigGolfCandidate.T3M.Search
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Defs ====
section

namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.T3M.Search (DIG NBUF ENC FailedAt KernAt)
open SigGolfCandidate.T3M.Expand (IDXV)
def PLAN : Nat := 0xff9a00
def PlanAt (t : MachineState) : Prop :=
  ∀ k < 128, t.getMem (BitVec.ofNat 64 (PLAN + 8 * k)) = bytesToWordLE ((planBytes.drop (8 * k)).take 8)
def zeroBlk : List (BitVec 32) := [28343,0x9a0eb823,0x9a0ebc23,0x9c0eb023,0x9c0eb423,2451,0xce4d606f]
def ExpandDataOK (im : Image) : Prop :=
  im.data = lplanBytes ++ planBytes ++ expCostBytes ++ hdrBankBytes ++ SigGolfCandidate.T3M.Images.expandLegacyData
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_ExpSearch ====
section

section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Search (DIG NBUF)
open SigGolfCandidate.T3M.Expand (IDXV)
open ClaudeWCT.W9.Machine.Sign (run)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE)
set_option maxRecDepth 100000
end ClaudeWCT.W9.Machine.Expand.ESearch
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF OutAt FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000 in
/-- Expand joint-cost cap test `S < 790` (nested FTS joint cap 789). -/
def capE : E := .bin .sltu (.reg .x20) (cst 790)
def resCap (d : Bool) : PRes :=
  ⟨⟨rfs [(.x6, capE)], [], []⟩, if d then pcOf 41060 else pcOf 41054, false, 2, 2, [⟨.eq, capE, .c 0, d⟩], none⟩
theorem chk_cap : (optBeq (run expLook [41060, 41054] 41052 [.br true]) (resCap true) &&
    optBeq (run expLook [41060, 41054] 41052 [.br false]) (resCap false)) = true := by decide +kernel
theorem run_cap (d : Bool) : run expLook [41060, 41054] 41052 [.br d] = some (resCap d) := by
  have h := chk_cap
  simp only [Bool.and_eq_true] at h
  cases d
  · exact optBeq_eq h.2
  · exact optBeq_eq h.1
theorem expCostBytes_length : expCostBytes.length = 16384 := by decide +kernel
section pieces
variable {im : Image}
theorem cap_spec (hl : LookOK im expLook) (s : MachineState) (hpc : s.pc = pcOf 41052) (S : Nat)
    (hS : S < 2 ^ 64) (h20 : s.getReg .x20 = BitVec.ofNat 64 S) :
    ∃ t, Steps im s 2 2 t ∧ t.pc = (if S ≤ 789 then pcOf 41054 else pcOf 41060) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _ => False) := by
  have hce : capE.eval s = BitVec.ofNat 64 (if S < 790 then 1 else 0) := by
    simp only [capE, cst, E.eval, h20, BinOp.eval, BitVec.ult, toNat_ofNat_lt hS,
      toNat_ofNat_lt (show 790 < 2 ^ 64 by decide +kernel)]
    by_cases h : S < 790 <;> simp [h]
  have hbr : ∀ b ∈ (resCap (decide ¬ (S ≤ 789))).brs, b.holds s := by
    intro b hb
    simp only [resCap, List.mem_singleton] at hb
    subst hb
    simp only [Br.holds, CmpOp.eval, E.eval, hce]
    by_cases h0 : S ≤ 789
    · simp only [show S < 790 by omega, if_true, h0, not_true_eq_false, decide_false]; decide +kernel
    · simp only [show ¬ S < 790 by omega, if_false, h0, not_false_eq_true, decide_true]; decide +kernel
  obtain ⟨hs, hp, -, hr, hm⟩ := piece hl (run_cap _) s hpc rfl hbr rfl
  refine ⟨_, hs, ?_, regs_rfs hr, fun A _ _ => by rw [hm]; rfl⟩
  rw [hp]; simp only [resCap]
  by_cases h0 : S ≤ 789
  · simp only [h0, not_true_eq_false, decide_false, Bool.false_eq_true, if_false, if_true]
  · simp only [h0, not_false_eq_true, decide_true, if_false, if_true]
end pieces
section loop
variable {im : Image} {sk : BitVec 256}
end loop
end ClaudeWCT.W9.Machine.Expand.ESearch
end
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Base ====
section

section
namespace ClaudeWCT.W9.Machine.Expand
open Lean Meta Elab Tactic
elab "krfl" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let lctx ← getLCtx
    let fvars := lctx.getFVarIds.filter fun f => !(lctx.get! f).isImplementationDetail
    let (_, g2) ← g.revert fvars (preserveOrder := true)
    g2.withContext do
      let t ← instantiateMVars (← g2.getType)
      if t.hasMVar then throwError "krfl: goal contains metavariables"
      let pf ← forallTelescope t fun xs body => do
        let some (_, lhs, _) := body.eq? | throwError "krfl: goal is not an equation"
        mkLambdaFVars xs (← mkEqRefl lhs)
      let name ← mkAuxLemma [] t pf
      g2.assign (mkConst name)
      replaceMainGoal []
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
def windowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i => expLook (n + i) == ws[i]?
theorem codeAt_of_look {im : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK im look) (n : Nat)
    (ws : List (BitVec 32)) (hn : 0x1000 + 4 * n + 4 * ws.length < 2 ^ 64)
    (h : ∀ i, i < ws.length → look (n + i) = ws[i]?) : CodeAt im (pcOf n) ws := by
  have hpc : (pcOf n).toNat = 0x1000 + 4 * n := by
    rw [pcOf, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨by omega, by omega, by omega, ?_⟩
  rw [hpc, show (0x1000 + 4 * n - 0x1000) / 4 = n by omega]
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ws.length
  · rw [List.getElem?_take, if_pos (by simpa using hi), List.getElem?_drop]
    have := hl (n + i) (ws[i]) (by rw [h i hi]; simp [hi])
    rw [this]; simp [hi]
  · rw [List.getElem?_eq_none (by omega)]
    by_cases hd : i < (List.drop n im.code).length
    · have := h
      rw [List.getElem?_take, if_neg (by simp; omega)]
    · rw [List.getElem?_eq_none (by simp at hd ⊢; omega)]
theorem pcOf_add_lit (n m k : Nat) (h : (0x1000 + 4 * n + k) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64) :
    pcOf n + BitVec.ofNat 64 k = pcOf m := by
  apply BitVec.eq_of_toNat_eq
  simp only [pcOf, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [← h]
  omega
theorem micro_step {im : Image} {pc : Word} {w : BitVec 32} {i : Instruction} {m : Micro}
    (hc : CodeAt im pc [w]) (hd : decodeInstruction w = some i) (hcl : classify i = some m)
    {s t : MachineState} (hpc : s.pc = pc) (he : m.exec s = some t) :
    Steps im s 1 (instructionCycles i) t := by
  have hf : fetch im s = some i := (hc.fetch s hpc).trans hd
  have := Steps.step (image := im) hf ((classify_sound hcl s).trans he) (Steps.refl t)
  simpa using this
theorem jal_x0_step {im : Image} {n m : Nat} {w : BitVec 32} {imm : BitVec 21}
    (hc : CodeAt im (pcOf n) [w]) (hd : decodeInstruction w = some (.base (.JAL .x0 imm)))
    (hoff : (0x1000 + 4 * n + (signExtend21 imm).toNat) % 2 ^ 64 = (0x1000 + 4 * m) % 2 ^ 64)
    (s : MachineState) (hpc : s.pc = pcOf n) : Steps im s 1 1 (s.setPC (pcOf m)) := by
  have h := micro_step (m := .jal .x0 (signExtend21 imm)) hc hd rfl hpc (t := s.setPC (pcOf m)) (by
    simp only [Micro.exec, MachineState.setReg, hpc, Option.some.injEq]
    have e : signExtend21 imm = BitVec.ofNat 64 (signExtend21 imm).toNat := by simp
    rw [e, pcOf_add_lit n m _ hoff])
  exact h
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_DrvBits ====
section

section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIG NBUF ENC)
set_option autoImplicit false
set_option maxRecDepth 8192
section blocks
variable (s : MachineState)
-- [h2 lane] removed s0_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
end SigGolfCandidate.T3M.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Search
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Expand (IDXV)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8192
theorem extractLsb'_256_toNat (a : BitVec 256) (w : Nat) :
    (a.extractLsb' (64 * w) 64).toNat = a.toNat / 2 ^ (64 * w) % 2 ^ 64 := by
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
theorem mod_div_mod (X k m : Nat) (h : k + m ≤ 64) : X % 2 ^ 64 / 2 ^ k % 2 ^ m = X / 2 ^ k % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < m
  · simp only [hi, decide_true, Bool.true_and]
    have : i + k < 64 := by omega
    simp [this]
  · simp [hi]
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
def base : Nat := 3164
def seg_0 : List (BitVec 32) := [16777327]
def seg_1 : List (BitVec 32) := [1049235,1049875,115]
def seg_4 : List (BitVec 32) := [100678403,125841795,52547987,19,0x5491b193]
def seg_9 : List (BitVec 32) := [0xfe0180e3]
def seg_10 : List (BitVec 32) := [727827,35347219,1049491,29038483,66359,6784947,2098835,3148179,4196883,5245587,6294803,7343891,34281619,5175,0x84040413,16772663,0x600e0e13,4407,0xffc10113,20151,0x4a4e8e93,52279,0x4a4c0c13,67110291]
def seg_34 : List (BitVec 32) := [0x6003803,545171,0x7f1f193,33657363,23224883,21077907,0xffefb3,8493971,31165363,0x60178d93,19,5789459,2586419,25626419,0x42000493,458983]
def seg_50 : List (BitVec 32) := [0x6803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x44000493,458983]
def seg_68 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x46000493,458983]
def seg_86 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x48000493,458983]
def seg_104 : List (BitVec 32) := [0x7003803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x4a000493,458983]
def seg_122 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x4c000493,458983]
def seg_140 : List (BitVec 32) := [60314003,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,43538195,2586419,25626419,0x4e000493,458983]
def seg_158 : List (BitVec 32) := [0x7803803,0x7f87193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,5789459,2586419,25626419,0x50000493,458983]
def seg_176 : List (BitVec 32) := [22565267,0x7f1f193,33657363,23224883,6784947,21077907,0xffefb3,8493971,31165363,0x40040413,537792019,0x60178d93,19,27809555,2586419,25626419,0x52000493,458983]
/-- Nested FTS (r1-1): the forest hash is replaced by copying `(L8, R8)` from the forest-buffer pair 8 (`0x520`) to
`0x100` (copied to the L3 encoding block by 39142) and to the encoding R slot `0x20290`; 203 is now a NOP. -/
def seg_194 : List (BitVec 32) := [1375744387,1384134403,271593507,283128867,1392521603,1400911619,134711,675166243,686701603]
def seg_203 : List (BitVec 32) := [19]
def seg_204 : List (BitVec 32) := [0x6f92206f]
def layout : SigGolfCandidate.Rv.Layout := [(0, seg_0), (1, seg_1), (4, seg_4), (9, seg_9), (10, seg_10), (34, seg_34), (50, seg_50), (68, seg_68), (86, seg_86), (104, seg_104), (122, seg_122), (140, seg_140), (158, seg_158), (176, seg_176), (194, seg_194), (203, seg_203), (204, seg_204)]
def code : List (BitVec 32) := layoutCode layout
theorem window : windowOK base code = true := by decide +kernel
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
theorem child_bits (a : BitVec 256) (w sh : Nat) (h : sh + 7 ≤ 64) :
    ((a.extractLsb' (64 * w) 64 >>> sh) &&& 127#64).toNat = a.toNat / 2 ^ (64 * w + sh) % 128 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, extractLsb'_256_toNat,
    show (127#64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    mod_div_mod _ _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rfl
end ClaudeWCT.W9.Machine.Expand
end
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Merkle_ChildDefs ====
section

namespace ClaudeWCT.W9.Machine.Merkle
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
open SigGolfCandidate.T3 (Digest HashOutput M header shortHash pad64)
open SphincsSecurity (bytesLE)
def bitAt (j l : Nat) : Nat := j / 2 ^ l % 2
def blkO (l : Nat) : Nat := 64 * (6 - l)
def curO (l j : Nat) : Nat := blkO l + 48 * bitAt j l
def sibO (l j : Nat) : Nat := blkO l + 48 * (1 - bitAt j l)
def padO (l : Nat) : Nat := blkO l + 32
def leafO : Nat := 816
def heapOf (l j : Nat) : Nat := 2 ^ (6 - l) + j / 2 ^ (l + 1)
/-- C4: FTS node words carry the coordinate nibble `k + 1`. -/
def nodeLo (k index : Nat) : Nat := 1537 + 65536 * (k + 1) + 2 ^ 27 * index
def heapReg (h : Nat) : Reg :=
  match h with
  | 2 => .x13 | 3 => .x19 | 4 => .x20 | 5 => .x21 | 6 => .x26 | _ => .x30
def leafBytes (leaf : Nat → Digest) : List UInt8 := (List.range 8).flatMap fun i => bytesLE 16 (leaf i)
def childLevel (k index j : Nat) (sibs : Nat → Digest) (value : Digest) (l : Nat) : M Digest :=
  let pair := if bitAt j l = 0 then (value, sibs l) else (sibs l, value)
  WCT9.wctNodeHash k index (heapOf l j) pair.1 pair.2
def pairOf (j : Nat) (top sib : Digest) : Digest × Digest := if bitAt j 6 = 0 then (top, sib) else (sib, top)
def childProgC (k index j : Nat) (leaf sibs : Nat → Digest) : M (Digest × Digest) := do
  let v ← shortHash (leafBytes leaf)
  let top ← (List.range 6).foldlM (childLevel k index j sibs) v
  pure (pairOf j top (sibs 6))
def stageW (j l : Nat) : List Nat :=
  [curO l j, curO l j + 8, curO l j + 16, curO l j + 24, blkO l + 16, blkO l + 24]
def stagesW (j n : Nat) : List Nat := (List.range n).flatMap (stageW j)
def childWrites (j : Nat) : List Nat := stagesW j 6
/-- The 8 leaf digests (T8): `end0 | header | pad (honest 0) | end1..end5`. -/
def leafFields (k index j : Nat) (ends : List Digest) (i : Nat) : Digest :=
  if i = 0 then ends.getD 0 0 else if i = 1 then ClaudeWCT.WCT9.ftsLeafHeader index k j
  else if i = 2 then 0 else ends.getD (i - 2) 0
def sixLevels (k index j : Nat) (path : Nat → Digest) (root : Digest) : M Digest :=
  (List.range 6).foldlM (fun value l =>
    let other := path l
    let pair := if j / 2 ^ l % 2 = 0 then (value, other) else (other, value)
    ClaudeWCT.WCT9.wctNodeHash k index (2 ^ (6 - l) + j / 2 ^ (l + 1)) pair.1 pair.2) root
def finPath (path : Fin 7 → Digest) (l : Nat) : Digest := if h : l < 7 then path ⟨l, h⟩ else 0
end ClaudeWCT.W9.Machine.Merkle
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Region ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput readDigest readLE)
open SigGolfCandidate.T3M (window window_append_left window_append_right window_full window_zeros zeros)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.T3M (chainBytes leafBytes)
set_option linter.unusedSimpArgs false
theorem wordsOf_getD (L : List UInt8) (m : Nat) (hL : L.length = 8 * m) (i : Nat) (hi : i < m) :
    (wordsOf L).getD i 0 = BitVec.ofNat 64 (readLE (window L (8 * i) 8)) := by
  rw [wordsOf_eq_range m L hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have hw : readLE (window L (8 * i) 8) < 2 ^ 64 := by
    have := readLE_lt (window L (8 * i) 8)
    have hl : (window L (8 * i) 8).length ≤ 8 := by unfold window; simp
    calc readLE (window L (8 * i) 8) < 256 ^ (window L (8 * i) 8).length := this
      _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt hw, show 2 ^ (64 * i) = 256 ^ (8 * i) by rw [pow_mul, pow_mul]; norm_num,
    SigGolfCandidate.T3M.readLE_drop, show 2 ^ 64 = 256 ^ 8 by norm_num, SigGolfCandidate.T3M.readLE_take]
  rfl
section windows
variable (c : Nat) (op : WCT9.Opening)
end windows
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_LayoutCode ====
section

/-! Pairing stage 1: code tables of the leaf / digest layout block 48100 .. 49225 (proofs in `LayoutBlock`). -/
namespace ClaudeWCT.W9.Machine.Expand.Layout
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
/-! Generated by pair1-expand (from sol-pair1/img-candidate/expand.code, words 48119 .. 49224).
T51 (VERA2, round 2; regenerated from the T51 expand image t51/sign/img/t51e, words 48119 .. 49225): the top group
keeps the 51 items of values 0..50 (item 129, value 0: `sd t1,-32(a1)`, so `xK 129 = 2^64 - 32` and its slot is
`(dK + xK) % 2^64 = 25200`; item 129 + i: `X = 16 (i - 1)`). #938's items 180..182 (values 51..53) lost their
stores (`nop`): with the return word they form the straight tail `cRet` (49207 .. 49225, 19 words). -/
def lbPc : List Nat := [48121,48127,48133,48139,48145,48151,48157,48163,48169,48175,48181,48187,48193,48199,48205,48211,48217,48223,48229,48235,48241,48247,48253,48259,48265,48271,48277,48283,48289,48295,48301,48307,48313,48319,48325,48331,48337,48343,48349,48355,48361,48367,48373,48381,48387,48393,48399,48405,48411,48417,48423,48429,48435,48441,48447,48453,48459,48465,48471,48477,48483,48489,48495,48501,48507,48513,48519,48525,48531,48537,48543,48549,48555,48561,48567,48573,48579,48585,48591,48597,48603,48609,48615,48621,48627,48633,48641,48647,48653,48659,48665,48671,48677,48683,48689,48695,48701,48707,48713,48719,48725,48731,48737,48743,48749,48755,48761,48767,48773,48779,48785,48791,48797,48803,48809,48815,48821,48827,48833,48839,48845,48851,48857,48863,48869,48875,48881,48887,48893,48901,48907,48913,48919,48925,48931,48937,48943,48949,48955,48961,48967,48973,48979,48985,48991,48997,49003,49009,49015,49021,49027,49033,49039,49045,49051,49057,49063,49069,49075,49081,49087,49093,49099,49105,49111,49117,49123,49129,49135,49141,49147,49153,49159,49165,49171,49177,49183,49189,49195,49201]
def lbS : List Nat := [22992,22856,22928,22752,22824,22648,22720,22544,22616,22440,22512,22336,22408,22232,22304,22128,22200,22024,22096,21920,21992,21816,21888,21712,21784,21608,21680,21504,21576,21400,21472,21296,21368,21192,21264,21088,21160,20984,21056,20880,20952,20776,20848,20424,20288,20360,20184,20256,20080,20152,19976,20048,19872,19944,19768,19840,19664,19736,19560,19632,19456,19528,19352,19424,19248,19320,19144,19216,19040,19112,18936,19008,18832,18904,18728,18800,18624,18696,18520,18592,18416,18488,18312,18384,18208,18280,17856,17720,17792,17616,17688,17512,17584,17408,17480,17304,17376,17200,17272,17096,17168,16992,17064,16888,16960,16784,16856,16680,16752,16576,16648,16472,16544,16368,16440,16264,16336,16160,16232,16056,16128,15952,16024,15848,15920,15744,15816,15640,15712,15208,15144,15080,15016,14952,14888,14824,14760,14696,14632,14568,14504,14440,14376,14312,14248,14184,14120,14056,13992,13928,13864,13800,13736,13672,13608,13544,13480,13416,13352,13288,13224,13160,13096,13032,12968,12904,12840,12776,12712,12648,12584,12520,12456,12392,12328,12264,12200,12136,12072,12008]
def lbX : List Nat := [0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,0,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,18446744073709551584,0,16,32,48,64,80,96,112,128,144,160,176,192,208,224,240,256,272,288,304,320,336,352,368,384,400,416,432,448,464,480,496,512,528,544,560,576,592,608,624,640,656,672,688,704,720,736,752,768,784]
def lbD : List Nat := [23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23008,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,23744,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,24480,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232,25232]
def lbCodes : List (List (BitVec 32)) := [[25911,2634351891,340739,6664227,8729347,6665251],[25911,2491745555,340739,40218659,8729347,40219683],[25911,2567243027,340739,40220707,8729347,40221731],[25911,2382693651,340739,73773091,8729347,73774115],[25911,2458191123,340739,73775139,8729347,73776163],[25911,2273641747,340739,107327523,8729347,107328547],[25911,2349139219,340739,107329571,8729347,107330595],[25911,2164589843,340739,140881955,8729347,140882979],[25911,2240087315,340739,140884003,8729347,140885027],[21815,2055537939,340739,174436387,8729347,174437411],[21815,2131035411,340739,174438435,8729347,174439459],[21815,1946486035,340739,207990819,8729347,207991843],[21815,2021983507,340739,207992867,8729347,207993891],[21815,1837434131,340739,241545251,8729347,241546275],[21815,1912931603,340739,241547299,8729347,241548323],[21815,1728382227,340739,275099683,8729347,275100707],[21815,1803879699,340739,275101731,8729347,275102755],[21815,1619330323,340739,308654115,8729347,308655139],[21815,1694827795,340739,308656163,8729347,308657187],[21815,1510278419,340739,342208547,8729347,342209571],[21815,1585775891,340739,342210595,8729347,342211619],[21815,1401226515,340739,375762979,8729347,375764003],[21815,1476723987,340739,375765027,8729347,375766051],[21815,1292174611,340739,409317411,8729347,409318435],[21815,1367672083,340739,409319459,8729347,409320483],[21815,1183122707,340739,442871843,8729347,442872867],[21815,1258620179,340739,442873891,8729347,442874915],[21815,1074070803,340739,476426275,8729347,476427299],[21815,1149568275,340739,476428323,8729347,476429347],[21815,965018899,340739,509980707,8729347,509981731],[21815,1040516371,340739,509982755,8729347,509983779],[21815,855966995,340739,543535139,8729347,543536163],[21815,931464467,340739,543537187,8729347,543538211],[21815,746915091,340739,577089571,8729347,577090595],[21815,822412563,340739,577091619,8729347,577092643],[21815,637863187,340739,610644003,8729347,610645027],[21815,713360659,340739,610646051,8729347,610647075],[21815,528811283,340739,644198435,8729347,644199459],[21815,604308755,340739,644200483,8729347,644201507],[21815,419759379,340739,677752867,8729347,677753891],[21815,495256851,340739,677754915,8729347,677755939],[21815,310707475,340739,711307299,8729347,711308323],[21815,386204947,340739,711309347,8729347,711310371],[21815,4236576019,340739,6664227,8729347,6665251],[21815,4093969683,340739,40218659,8729347,40219683],[21815,4169467155,340739,40220707,8729347,40221731],[21815,3984917779,340739,73773091,8729347,73774115],[21815,4060415251,340739,73775139,8729347,73776163],[21815,3875865875,340739,107327523,8729347,107328547],[21815,3951363347,340739,107329571,8729347,107330595],[21815,3766813971,340739,140881955,8729347,140882979],[21815,3842311443,340739,140884003,8729347,140885027],[21815,3657762067,340739,174436387,8729347,174437411],[21815,3733259539,340739,174438435,8729347,174439459],[21815,3548710163,340739,207990819,8729347,207991843],[21815,3624207635,340739,207992867,8729347,207993891],[21815,3439658259,340739,241545251,8729347,241546275],[21815,3515155731,340739,241547299,8729347,241548323],[21815,3330606355,340739,275099683,8729347,275100707],[21815,3406103827,340739,275101731,8729347,275102755],[21815,3221554451,340739,308654115,8729347,308655139],[21815,3297051923,340739,308656163,8729347,308657187],[21815,3112502547,340739,342208547,8729347,342209571],[21815,3188000019,340739,342210595,8729347,342211619],[21815,3003450643,340739,375762979,8729347,375764003],[21815,3078948115,340739,375765027,8729347,375766051],[21815,2894398739,340739,409317411,8729347,409318435],[21815,2969896211,340739,409319459,8729347,409320483],[21815,2785346835,340739,442871843,8729347,442872867],[21815,2860844307,340739,442873891,8729347,442874915],[21815,2676294931,340739,476426275,8729347,476427299],[21815,2751792403,340739,476428323,8729347,476429347],[21815,2567243027,340739,509980707,8729347,509981731],[21815,2642740499,340739,509982755,8729347,509983779],[21815,2458191123,340739,543535139,8729347,543536163],[21815,2533688595,340739,543537187,8729347,543538211],[21815,2349139219,340739,577089571,8729347,577090595],[21815,2424636691,340739,577091619,8729347,577092643],[21815,2240087315,340739,610644003,8729347,610645027],[21815,2315584787,340739,610646051,8729347,610647075],[17719,2131035411,340739,644198435,8729347,644199459],[21815,2206532883,340739,644200483,8729347,644201507],[17719,2021983507,340739,677752867,8729347,677753891],[17719,2097480979,340739,677754915,8729347,677755939],[17719,1912931603,340739,711307299,8729347,711308323],[17719,1988429075,340739,711309347,8729347,711310371],[17719,1543832851,340739,6664227,8729347,6665251],[17719,1401226515,340739,40218659,8729347,40219683],[17719,1476723987,340739,40220707,8729347,40221731],[17719,1292174611,340739,73773091,8729347,73774115],[17719,1367672083,340739,73775139,8729347,73776163],[17719,1183122707,340739,107327523,8729347,107328547],[17719,1258620179,340739,107329571,8729347,107330595],[17719,1074070803,340739,140881955,8729347,140882979],[17719,1149568275,340739,140884003,8729347,140885027],[17719,965018899,340739,174436387,8729347,174437411],[17719,1040516371,340739,174438435,8729347,174439459],[17719,855966995,340739,207990819,8729347,207991843],[17719,931464467,340739,207992867,8729347,207993891],[17719,746915091,340739,241545251,8729347,241546275],[17719,822412563,340739,241547299,8729347,241548323],[17719,637863187,340739,275099683,8729347,275100707],[17719,713360659,340739,275101731,8729347,275102755],[17719,528811283,340739,308654115,8729347,308655139],[17719,604308755,340739,308656163,8729347,308657187],[17719,419759379,340739,342208547,8729347,342209571],[17719,495256851,340739,342210595,8729347,342211619],[17719,310707475,340739,375762979,8729347,375764003],[17719,386204947,340739,375765027,8729347,375766051],[17719,201655571,340739,409317411,8729347,409318435],[17719,277153043,340739,409319459,8729347,409320483],[17719,92603667,340739,442871843,8729347,442872867],[17719,168101139,340739,442873891,8729347,442874915],[17719,4278519059,340739,476426275,8729347,476427299],[17719,59049235,340739,476428323,8729347,476429347],[17719,4169467155,340739,509980707,8729347,509981731],[17719,4244964627,340739,509982755,8729347,509983779],[17719,4060415251,340739,543535139,8729347,543536163],[17719,4135912723,340739,543537187,8729347,543538211],[17719,3951363347,340739,577089571,8729347,577090595],[17719,4026860819,340739,577091619,8729347,577092643],[17719,3842311443,340739,610644003,8729347,610645027],[17719,3917808915,340739,610646051,8729347,610647075],[17719,3733259539,340739,644198435,8729347,644199459],[17719,3808757011,340739,644200483,8729347,644201507],[17719,3624207635,340739,677752867,8729347,677753891],[17719,3699705107,340739,677754915,8729347,677755939],[17719,3515155731,340739,711307299,8729347,711308323],[17719,3590653203,340739,711309347,8729347,711310371],[17719,3062170899,340739,4268077091,8729347,4268078115],[17719,2995062035,340739,6664227,8729347,6665251],[17719,2927953171,340739,6666275,8729347,6667299],[17719,2860844307,340739,40218659,8729347,40219683],[17719,2793735443,340739,40220707,8729347,40221731],[17719,2726626579,340739,73773091,8729347,73774115],[17719,2659517715,340739,73775139,8729347,73776163],[17719,2592408851,340739,107327523,8729347,107328547],[17719,2525299987,340739,107329571,8729347,107330595],[17719,2458191123,340739,140881955,8729347,140882979],[17719,2391082259,340739,140884003,8729347,140885027],[17719,2323973395,340739,174436387,8729347,174437411],[17719,2256864531,340739,174438435,8729347,174439459],[17719,2189755667,340739,207990819,8729347,207991843],[13623,2122646803,340739,207992867,8729347,207993891],[13623,2055537939,340739,241545251,8729347,241546275],[13623,1988429075,340739,241547299,8729347,241548323],[13623,1921320211,340739,275099683,8729347,275100707],[13623,1854211347,340739,275101731,8729347,275102755],[13623,1787102483,340739,308654115,8729347,308655139],[13623,1719993619,340739,308656163,8729347,308657187],[13623,1652884755,340739,342208547,8729347,342209571],[13623,1585775891,340739,342210595,8729347,342211619],[13623,1518667027,340739,375762979,8729347,375764003],[13623,1451558163,340739,375765027,8729347,375766051],[13623,1384449299,340739,409317411,8729347,409318435],[13623,1317340435,340739,409319459,8729347,409320483],[13623,1250231571,340739,442871843,8729347,442872867],[13623,1183122707,340739,442873891,8729347,442874915],[13623,1116013843,340739,476426275,8729347,476427299],[13623,1048904979,340739,476428323,8729347,476429347],[13623,981796115,340739,509980707,8729347,509981731],[13623,914687251,340739,509982755,8729347,509983779],[13623,847578387,340739,543535139,8729347,543536163],[13623,780469523,340739,543537187,8729347,543538211],[13623,713360659,340739,577089571,8729347,577090595],[13623,646251795,340739,577091619,8729347,577092643],[13623,579142931,340739,610644003,8729347,610645027],[13623,512034067,340739,610646051,8729347,610647075],[13623,444925203,340739,644198435,8729347,644199459],[13623,377816339,340739,644200483,8729347,644201507],[13623,310707475,340739,677752867,8729347,677753891],[13623,243598611,340739,677754915,8729347,677755939],[13623,176489747,340739,711307299,8729347,711308323],[13623,109380883,340739,711309347,8729347,711310371],[13623,42272019,340739,744861731,8729347,744862755],[13623,4270130451,340739,744863779,8729347,744864803],[13623,4203021587,340739,778416163,8729347,778417187],[13623,4135912723,340739,778418211,8729347,778419235],[13623,4068803859,340739,811970595,8729347,811971619],[13623,4001694995,340739,811972643,8729347,811973667]]
def lbHeadPc : List Nat := [48119,48379,48639,48899]
def lbHeadCodes : List (List (BitVec 32)) := [[26039,2651162003],[26039,3422913939],[26039,4194665875],[26039,688227731]]
def cTop : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593,0x00053303,0x0065b023,0x00853303,
  0x0065b423,0x01053303,0x0065b823,0x01853303,0x0065bc23]
def cClr0 : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593]
def cClrL : List (BitVec 32) := [0x00053023,0x00850513,0xfeb56ce3]
def cRet : List (BitVec 32) := [0x00003537,0xea850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe6850513,0x00053303,0x00000013,0x00853303,0x00000013,0x00003537,0xe2850513,0x00053303,0x00000013,0x00853303,0x00000013,0xe8cfa06f]
def pcK (k : Nat) : Nat := lbPc.getD k 0
def sK (k : Nat) : Nat := lbS.getD k 0
def xK (k : Nat) : Nat := lbX.getD k 0
def dK (k : Nat) : Nat := lbD.getD k 0
def slotK (k : Nat) : Nat := (dK k + xK k) % 2 ^ 64
/-- Item `k` starts with a group head `li a1,D` (k = 0, 43, 86, 129). -/
def hdK (k : Nat) : Bool := k == 0 || k == 43 || k == 86 || k == 129
def grpK (k : Nat) : Nat := if k < 43 then 0 else if k < 86 then 1 else if k < 129 then 2 else 3
/-- Start pc of item `k` (its head, if any). -/
def itemPc (k : Nat) : Nat := if hdK k then pcK k - 2 else pcK k
def itemLen (k : Nat) : Nat := if hdK k then 8 else 6
theorem tab_facts : (∀ k < 180, pcK k + 6 = itemPc (k + 1) ∨ k = 179) ∧ pcK 179 + 6 = 49207 ∧ itemPc 0 = 48119 ∧
    (∀ k < 180, hdK k = true → (lbHeadPc.getD (grpK k) 0 = pcK k - 2)) ∧
    (∀ k < 180, hdK k = false → 0 < k ∧ dK k = dK (k - 1)) ∧
    (∀ k < 179, slotK k + 16 ≤ slotK (k + 1)) ∧ 23008 ≤ slotK 0 ∧ slotK 179 + 16 ≤ 26112 ∧
    (∀ k < 180, sK k % 8 = 0 ∧ sK k + 16 ≤ 23008 ∧ xK k % 8 = 0 ∧ xK k < 2 ^ 64 ∧ dK k % 8 = 0 ∧ dK k < 2 ^ 64) := by
  refine ⟨?_, by decide, by decide, ?_, ?_, ?_, by decide, by decide, ?_⟩ <;> decide
/-- The block's code. -/
structure Code (im : Image) : Prop where
  top : CodeAt im (pcOf 48100) cTop
  clr0 : CodeAt im (pcOf 48112) cClr0
  clrL : CodeAt im (pcOf 48116) cClrL
  head : ∀ g < 4, CodeAt im (pcOf (lbHeadPc.getD g 0)) (lbHeadCodes.getD g [])
  chunk : ∀ k < 180, CodeAt im (pcOf (pcK k)) (lbCodes.getD k [])
  ret : CodeAt im (pcOf 49207) cRet
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

/-- Code words of the compact/nested-FTS expansion that the paired expander keeps from the reference image. Stage 2
(C2 + C3, from #866): also the trampolines `43472 .. 43488` (`Compact2.cETail`, the footer's LE64(1) at `WIT + 24`,
and `Compact2.cRT 1..3`, the lower root windows' row-tweak pads). -/
def compactScope (n : Nat) : Bool :=
  decide ((33000≤n ∧ n<33285) ∨ (41108≤n ∧ n<42719) ∨ (43472≤n ∧ n<43489) ∨ (43951≤n ∧ n≤44043) ∨ (43500≤n ∧ n<43761))
def compactLook (n : Nat) : Option (BitVec 32) := if compactScope n then expLook n else none
namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
def cPC0 : List (BitVec 32) := [0x01500613]
def cPCL : List (BitVec 32) := [0x03053303,0x0465bc23,0x03853303,0x0665b023,0x07053303,0x0065b823,0x07853303,
  0x0065bc23,0x08050513,0x06858593,0xfff60613,0xfc061ae3]
def cPCT : List (BitVec 32) := [0x03053303,0x0265b823,0x03853303,0x0265bc23,0x00008067]
/-- The pair copy block's code (head, loop body, tail). -/
structure Code (im : Image) : Prop where
  c0 : CodeAt im (pcOf 48000) cPC0
  cL : CodeAt im (pcOf 48001) cPCL
  cT : CodeAt im (pcOf 48013) cPCT
end PairCopy
structure CompactCodeAt (im : Image) : Prop where
  look : LookOK im compactLook
  /-- Pairing stage 1: the pair copy block 48000 .. 48017. -/
  pair : PairCopy.Code im
  /-- Pairing stage 1: the leaf / digest layout block 48100 .. 49225. -/
  layout : Layout.Code im

theorem CompactCodeAt.ofNew {im : Image} (h : NewCodeAt im) (hp : PairCopy.Code im) (hl : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hp, hl⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · exact expLook_ok h n w hw
  · cases hw

def compactWindowOK (n : Nat) (ws : List (BitVec 32)) : Bool :=
  (List.range ws.length).all fun i=>compactLook (n+i)==ws[i]?
theorem codeAt_of_compact_window {im : Image} (hc : CompactCodeAt im) {n : Nat} {ws : List (BitVec 32)}
    (hn : 0x1000+4*n+4*ws.length<2^64) (h : compactWindowOK n ws=true) : CodeAt im (pcOf n) ws := by
  refine codeAt_of_look hc.look n ws hn (fun i hi=>?_)
  unfold compactWindowOK at h
  have:=List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simpa using this
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
def cfgC : Config := { noAlias := true }
/-- Nested FTS (r1-1): hold slot of coordinate `k` (top sibling, flag `1 - bit6`), written by the staging pass. -/
def holdAt (k : Nat) : Nat := 0x380000 + 32 * k
def coordAt (k : Nat) : Nat := 41121 + 111 * k
def sibAt (k l : Nat) : Nat := coordAt k + 13 + 14 * l
def sibLen (l : Nat) : Nat := if l < 6 then 14 else 12
def cStart : List (BitVec 32) := [5431,0x84050513,2098615,361875,1591,0x48060613,0x7e1000ef]
def cRegs : List (BitVec 32) := [2098231,263187,5303,0x84048493,0xffa937,0xa0090913]
def cRow : List (BitVec 32) := [66712467,4428691,7932467]
def cStep : List (BitVec 32) := [0x40040413,939820179]
def cFinal : List (BitVec 32) := [13623,0xc4050513,9655,0x7c058593,1591,0x6b160613,16777455]
def cHalt : List (BitVec 32) := [62914671]
def cCopy : List (BitVec 32) := [340739,6664227,8717587,8750483,0xfff60613,0xfe0616e3,32871]
def cZero : List (BitVec 32) := [372771,8750483,0xfff60613,0xfe061ae3,32871]
def cHeads : List (List (BitVec 32)) :=[[0x6003303,217875,0x7f37993,296339,41944595,0x7cd000ef],[0x6803303,217875,0x7f37993,296339,41944595,0x611000ef],[0x6803303,22237971,0x7f37993,296339,41944595,0x455000ef],[0x6803303,59986707,0x7f37993,296339,41944595,697303279],[0x7003303,217875,0x7f37993,296339,41944595,0xdd000ef],[0x7003303,22237971,0x7f37993,296339,41944595,0x720000ef],[0x7003303,59986707,0x7f37993,296339,41944595,0x564000ef],[0x7803303,217875,0x7f37993,296339,41944595,981467375],[0x7803303,22237971,0x7f37993,296339,41944595,515899631]]
def cHead (k : Nat) : List (BitVec 32) := cHeads.getD k []
def cMids : List (List (BitVec 32)) :=[[470025491,335840659,75499027,0x7a1000ef],[470025491,335840659,75499027,0x5e5000ef],[470025491,335840659,75499027,0x429000ef],[470025491,335840659,75499027,651165935],[470025491,335840659,75499027,0xb1000ef],[470025491,335840659,75499027,0x6f4000ef],[470025491,335840659,75499027,0x538000ef],[470025491,335840659,75499027,935330031],[470025491,335840659,75499027,469762287]]
def cMid (k : Nat) : List (BitVec 32) := cMids.getD k []
/-- r3w (witness stack): the sibling blocks now differ per coordinate (store immediates `-sh k l`), index `6 k + l`. -/
def cSibs : List (List (BitVec 32)) :=[[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,31338531,32388131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,31338531,32388131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4259199011,4260248611],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4259199011,4260248611],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4259199011,4260248611],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4259199011,4260248611],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4259199011,4260248611],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4259199011,4260248611],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4225642531,4226692131],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4225642531,4226692131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4225642531,4226692131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4225642531,4226692131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4225642531,4226692131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4225642531,4226692131],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4158535715,4159585315],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4158535715,4159585315],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4158535715,4159585315],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4158535715,4159585315],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4158535715,4159585315],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4158535715,4159585315],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4124979235,4126028835],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4124979235,4126028835],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4124979235,4126028835],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4124979235,4126028835],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4124979235,4126028835],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4124979235,4126028835],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4057872419,4058922019],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4057872419,4058922019],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4057872419,4058922019],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4057872419,4058922019],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4057872419,4058922019],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4057872419,4058922019],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,4024315939,4025365539],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,4024315939,4025365539],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,4024315939,4025365539],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,4024315939,4025365539],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,4024315939,4025365539],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,4024315939,4025365539],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3957209123,3958258723],[679427,29658675,647059,2097043,2084755,6264467,5218195,14651315,32769715,33426995,403095171,411483907,3957209123,3958258723],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,14651315,32769715,33426995,335986307,344375043,3957209123,3958258723],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,14651315,32769715,33426995,268877443,277266179,3957209123,3958258723],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,14651315,32769715,33426995,201768579,210157315,3957209123,3958258723],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,14651315,32769715,33426995,134659715,143048451,3957209123,3958258723],[872418835,29658675,5889939,2097043,2084755,6264467,5218195,14651315,32769715,33426995,67550851,75939587,3923652643,3924702243]]
def cSib (k l : Nat) : List (BitVec 32) := cSibs.getD (6 * k + l) []
section code
variable {im : Image} (hc : CompactCodeAt im)
include hc
theorem code_cStart : CodeAt im (pcOf 41108) cStart := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRegs : CodeAt im (pcOf 41115) cRegs := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cFinal : CodeAt im (pcOf 42120) cFinal := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHalt : CodeAt im (pcOf 42127) cHalt := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCopy : CodeAt im (pcOf 42130) cCopy := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero : CodeAt im (pcOf 42137) cZero := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_copyRet : CodeAt im (pcOf 42136) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_zeroRet : CodeAt im (pcOf 42141) [0x8067] := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHead (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k)) (cHead k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cMid (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 6)) (cMid k) := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 10)) cRow := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cStep (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 109)) cStep := by
  interval_cases k <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
/-- Nested FTS (r1-1): levels 0..5 run in place (level 5 now writes to the fixed staging block at +832); level 6
jumps to a per-coordinate trampoline (`sib6_spec`). -/
theorem code_cSib (k l : Nat) (hk : k < 9) (hl : l < 6) : CodeAt im (pcOf (sibAt k l)) (cSib k l) := by
  interval_cases k <;> interval_cases l <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
sym_block RStart := symRun cfgC cStart (pcOf 41108) 40
sym_block RRegs := symRun cfgC cRegs (pcOf 41115) 40
sym_block RFinal := symRun cfgC cFinal (pcOf 42120) 40
sym_block RHalt := symRun cfgC cHalt (pcOf 42127) 40
sym_block RCopy := symRun cfgC cCopy (pcOf 42130) 40
sym_block RCopyRet := symRun cfgC [0x8067] (pcOf 42136) 40
sym_block RZero := symRun cfgC cZero (pcOf 42137) 40
sym_block RZeroRet := symRun cfgC [0x8067] (pcOf 42141) 40
sym_block RHead0 := symRun cfgC (cHead 0) (pcOf (coordAt 0)) 40
sym_block RMid0 := symRun cfgC (cMid 0) (pcOf (coordAt 0 + 6)) 40
sym_block RHead1 := symRun cfgC (cHead 1) (pcOf (coordAt 1)) 40
sym_block RMid1 := symRun cfgC (cMid 1) (pcOf (coordAt 1 + 6)) 40
sym_block RHead2 := symRun cfgC (cHead 2) (pcOf (coordAt 2)) 40
sym_block RMid2 := symRun cfgC (cMid 2) (pcOf (coordAt 2 + 6)) 40
sym_block RHead3 := symRun cfgC (cHead 3) (pcOf (coordAt 3)) 40
sym_block RMid3 := symRun cfgC (cMid 3) (pcOf (coordAt 3 + 6)) 40
sym_block RHead4 := symRun cfgC (cHead 4) (pcOf (coordAt 4)) 40
sym_block RMid4 := symRun cfgC (cMid 4) (pcOf (coordAt 4 + 6)) 40
sym_block RHead5 := symRun cfgC (cHead 5) (pcOf (coordAt 5)) 40
sym_block RMid5 := symRun cfgC (cMid 5) (pcOf (coordAt 5 + 6)) 40
sym_block RHead6 := symRun cfgC (cHead 6) (pcOf (coordAt 6)) 40
sym_block RMid6 := symRun cfgC (cMid 6) (pcOf (coordAt 6 + 6)) 40
sym_block RHead7 := symRun cfgC (cHead 7) (pcOf (coordAt 7)) 40
sym_block RMid7 := symRun cfgC (cMid 7) (pcOf (coordAt 7 + 6)) 40
sym_block RHead8 := symRun cfgC (cHead 8) (pcOf (coordAt 8)) 40
sym_block RMid8 := symRun cfgC (cMid 8) (pcOf (coordAt 8 + 6)) 40
sym_block RRow := symRun cfgC cRow (pcOf (coordAt 0 + 10)) 40
sym_block RStep := symRun cfgC cStep (pcOf (coordAt 0 + 109)) 40
theorem run_row (k : Nat) (hk : k < 9) : symRun cfgC cRow (pcOf (coordAt k + 10)) 40 =
    some ⟨RRow.res.st, .c (pcOf (coordAt k + 13)), .endOfCode, 3, 3⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_step (k : Nat) (hk : k < 9) : symRun cfgC cStep (pcOf (coordAt k + 109)) 40 =
    some ⟨RStep.res.st, .c (pcOf (coordAt k + 111)), .endOfCode, 2, 2⟩ := by
  interval_cases k <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
def compactChunkAllowed (c : Nat) : Prop :=
  c=128 ∨ c=129 ∨ c=130 ∨ (160≤c ∧ c≤166) ∨ c=169 ∨ c=170 ∨ c=171 ∨ c=172
/-- Window `[compactChunkLo c, compactChunkLen c)` of image chunk `c` used by `compactScope` (chunk 169 only for the
stage-2 trampolines and C4 prefix; chunk 170 stops before the paired suffix jump at 43761). -/
def compactChunkLo (c : Nat) : Nat := if c=169 then 208 else 0
def compactChunkLen (c : Nat) : Nat := if c=172 then 12 else if c=170 then 241 else 256
theorem compactCode_of_chunks {im : Image}
    (hc : ∀c,compactChunkAllowed c → CodeAt im (pcOf (256*c+compactChunkLo c))
      (((expChunks.getD (c-4) []).take (compactChunkLen c)).drop (compactChunkLo c)))
    (hpair : PairCopy.Code im) (hlay : Layout.Code im) :
    CompactCodeAt im := by
  refine ⟨?_, hpair, hlay⟩
  intro n w hw
  unfold compactLook at hw
  split at hw
  · rename_i hs
    have hn := of_decide_eq_true hs
    have ha : compactChunkAllowed (n/256) := by unfold compactChunkAllowed; omega
    have hlo : compactChunkLo (n/256) ≤ n%256 := by unfold compactChunkLo; split <;> omega
    have hlo' : compactChunkLo (n/256) < 256 := by unfold compactChunkLo; split <;> omega
    have hl : n%256<compactChunkLen (n/256) := by unfold compactChunkLen; split_ifs <;> omega
    have hp : 1024≤n := by omega
    unfold expLook at hw
    rw [if_pos hp] at hw
    have ht : (((expChunks.getD (n/256-4) []).take (compactChunkLen (n/256))).drop
        (compactChunkLo (n/256)))[n%256-compactChunkLo (n/256)]?=some w := by
      rw [List.getElem?_drop,show compactChunkLo (n/256)+(n%256-compactChunkLo (n/256))=n%256 by omega,
        List.getElem?_take,if_pos hl]
      exact hw
    have hb : (pcOf (256*(n/256)+compactChunkLo (n/256))).toNat=0x1000+4*(256*(n/256)+compactChunkLo (n/256)) := by
      rw [pcOf,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]; omega
    obtain ⟨_,_,_,hpre⟩ := hc (n/256) ha
    rw [hb] at hpre
    obtain ⟨rest,hrest⟩ := hpre
    have hh := congrArg (·[n%256-compactChunkLo (n/256)]?) hrest
    simp only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ht).1,ht,List.getElem?_drop] at hh
    rw [show (0x1000+4*(256*(n/256)+compactChunkLo (n/256))-0x1000)/4+(n%256-compactChunkLo (n/256))=n by omega] at hh
    exact hh.symm
  · cases hw
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cSnap : List (BitVec 32) := [5431,2147812627,3212727,361875,5687,2861958675,4221563119]
def cZero2 : List (BitVec 32) := [1463,1208321427,5687,3276146195,4229951727]  -- nested FTS: zero 2718 words from 1216
/-- Nested FTS (r1-1): the header copy is replaced by `jal zero,P_final` (P_final at words 33117..33284). -/
def cHdr : List (BitVec 32) := [2899275887]
def cCtr : List (BitVec 32) := [3212599,33883411,1241515411,2098707,1280344303]
def cPRegs : List (List (BitVec 32)) := [[3212599,67437843,9655,2055570835,117442067,1255178479],[3212599,1006961939,9655,1116046739,117442067,1230012655],[3212599,1946486035,9655,176522643,117442067,1204846831],[3216695,2886010131,9655,3531965843,117442067,1179681007],[3216695,3825534227,9655,2592441747,117442067,1154515183],[3216695,470091027,5559,1652917651,117442067,1129349359],[3216695,1409615123,5559,713393555,117442067,1104183535],[3220791,2349139219,5559,4068836755,117442067,1079017711],[3220791,3288663315,5559,3129312659,117442067,1053851887]]
def cHolds : List (List (BitVec 32)) := [[3673655,17710979,933507,9322243,8361619,5218195,32933555,9015,201523987,6719155,4023824419,4024874019],[3673655,51265411,34487939,42876675,8361619,5218195,32933555,9015,3556967187,6719155,4057380899,4058430499],[3673655,84819843,68042371,76431107,8361619,5218195,32933555,9015,2617443091,6719155,4124487715,4125537315],[3673655,118374275,101596803,109985539,8361619,5218195,32933555,4919,1677918995,6719155,4158044195,4159093795],[3673655,151928707,135151235,143539971,8361619,5218195,32933555,4919,738394899,6719155,4225151011,4226200611],[3673655,185483139,168705667,177094403,8361619,5218195,32933555,4919,4093838099,6719155,4258707491,4259757091],[3673655,219037571,202260099,210648835,8361619,5218195,32933555,4919,3154314003,6719155,30847011,31896611],[3673655,252592003,235814531,244203267,8361619,5218195,32933555,4919,2214789907,6719155,30847011,31896611],[3673655,286146435,269368963,277757699,8361619,5218195,32933555,823,1275265811,6719155,30847011,31896611]]
def cPEnd : List (BitVec 32) := [990937199]
def cPReg (c : Nat) : List (BitVec 32) := cPRegs.getD c []
def cHold (c : Nat) : List (BitVec 32) := cHolds.getD c []
def pregAt (c : Nat) : Nat := 33122 + 6 * c
def holdPc (c : Nat) : Nat := 33176 + 12 * c
def cTop : List (BitVec 32) := [3220791,4236576019,13751,2944763283,1591,554042899,3877630191]
def cIdx : List (BitVec 32) := [0x6003b03,35347219,0xff9937,0x40090913]
def cCh1 : List (BitVec 32) := [3224887,545588499,17847,3498411411,1591,361104915,533745903]
def cRow1 : List (BitVec 32) := [0xcb5993,0x7f9f993,3774995,19532339,537528851]
def cLv10 : List (BitVec 32) := [3224887,478479635,672515,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv11 : List (BitVec 32) := [3224887,411370771,1721091,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv12 : List (BitVec 32) := [3224887,344261907,2769667,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv13 : List (BitVec 32) := [3224887,277153043,3818243,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv14 : List (BitVec 32) := [3224887,210044179,4866819,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv15 : List (BitVec 32) := [3224887,142935315,5915395,4395795,17847,3078981011,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv16 : List (BitVec 32) := [3224887,75826451,6963971,4395795,17847,3078981011,6653363,33898115,42286851,64335907,243273839,6935315,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh2 : List (BitVec 32) := [3228983,3833922835,17847,1896187283,1591,361104915,1954566383]
def cRow2 : List (BitVec 32) := [7035283,66714003,3774995,19532339]
def cLv20 : List (BitVec 32) := [3228983,3766813971,672515,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv21 : List (BitVec 32) := [3228983,3699705107,1721091,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv22 : List (BitVec 32) := [3228983,3632596243,2769667,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv23 : List (BitVec 32) := [3228983,3565487379,3818243,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv24 : List (BitVec 32) := [3228983,3498378515,4866819,4395795,17847,1560642963,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv25 : List (BitVec 32) := [3228983,3431269651,5915395,4395795,17847,1560642963,6653363,33898115,42286851,64335907,1783627887,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh3 : List (BitVec 32) := [3233079,2827289875,21943,293963155,1591,361104915,1329615087]
def cRow3 : List (BitVec 32) := [66812307,3774995,19532339]
def cLv30 : List (BitVec 32) := [3233079,2760181011,672515,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv31 : List (BitVec 32) := [3233079,2693072147,1721091,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv32 : List (BitVec 32) := [3233079,2625963283,2769667,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv33 : List (BitVec 32) := [3233079,2558854419,3818243,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv34 : List (BitVec 32) := [3233079,2491745555,4866819,4395795,21943,4253386131,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv35 : List (BitVec 32) := [3233079,2424636691,5915395,4395795,21943,4253386131,6653363,33898115,42286851,64335907,1179648111,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cTail : List (BitVec 32) := [3212599,328979,26039,2651162003,343683,8732419,30781475,31831075,17133187,374819,30784547]
def lvAt (lay j : Nat) : Nat := if lay = 1 then 42247 + 23 * j else if lay = 2 then 42419 + 23 * j else 42567 + 23 * j
def cLvs : List (List (BitVec 32)) := [cLv10, cLv11, cLv12, cLv13, cLv14, cLv15, cLv16, cLv20, cLv21, cLv22, cLv23, cLv24, cLv25, cLv30, cLv31, cLv32, cLv33, cLv34, cLv35]
def lvIdx (lay j : Nat) : Nat := if lay = 1 then j else if lay = 2 then 7 + j else 13 + j
def cLv (lay j : Nat) : List (BitVec 32) := cLvs.getD (lvIdx lay j) []
/-- C3 (FULL, E6): the root level of each lower layer jumps after its Z-pad copy to a trampoline that writes LE64(1)
at window + 24 (the encoding row tweak's high word, honest 1) and returns. -/
def rtAt (lay : Nat) : Nat := if lay = 1 then 43477 else if lay = 2 then 43481 else 43485
def cRT (lay : Nat) : List (BitVec 32) :=
  if lay = 1 then [65385507,1052307,30784547,4045398127] else if lay = 2 then [65385507,1052307,30784547,2505044079]
  else [65385507,1052307,30784547,3109023855]
def rootJ (lay : Nat) : Nat := if lay = 1 then 6 else 5
def cLvA (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).take 11
def cLvB (lay : Nat) : List (BitVec 32) := (cLv lay (rootJ lay)).drop 11
section code
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
theorem code_cSnap : CodeAt im (pcOf 42142) cSnap := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cZero2 : CodeAt im (pcOf 42149) cZero2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHdr : CodeAt im (pcOf 42154) cHdr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTop : CodeAt im (pcOf 42224) cTop := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCtr : CodeAt im (pcOf 33117) cCtr := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPEnd : CodeAt im (pcOf 33284) cPEnd := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cPReg (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (pregAt c)) (cPReg c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cHold (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (holdPc c)) (cHold c) := by
  interval_cases c <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cIdx : CodeAt im (pcOf 42231) cIdx := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh1 : CodeAt im (pcOf 42235) cCh1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow1 : CodeAt im (pcOf 42242) cRow1 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh2 : CodeAt im (pcOf 42408) cCh2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow2 : CodeAt im (pcOf 42415) cRow2 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cCh3 : CodeAt im (pcOf 42557) cCh3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRow3 : CodeAt im (pcOf 42564) cRow3 := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cTail : CodeAt im (pcOf 42705) cTail := codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < (if lay = 1 then 7 else 6)) :
    CodeAt im (pcOf (lvAt lay j)) (cLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (lvAt lay (rootJ lay))) (cLvA lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cLvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    CodeAt im (pcOf (lvAt lay (rootJ lay) + 11)) (cLvB lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
theorem code_cRT (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (rtAt lay)) (cRT lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_compact_window hc (by decide) (by decide +kernel)
end code
sym_block RIdx := symRun cfgC cIdx (pcOf 42231) 40
sym_block RRow1 := symRun cfgC cRow1 (pcOf 42242) 40
sym_block RRow2 := symRun cfgC cRow2 (pcOf 42415) 40
sym_block RRow3 := symRun cfgC cRow3 (pcOf 42564) 40
sym_block RTail := symRun cfgC cTail (pcOf 42705) 40
sym_block RLv10 := symRun cfgC (cLv 1 0) (pcOf (lvAt 1 0)) 40
sym_block RLv11 := symRun cfgC (cLv 1 1) (pcOf (lvAt 1 1)) 40
sym_block RLv12 := symRun cfgC (cLv 1 2) (pcOf (lvAt 1 2)) 40
sym_block RLv13 := symRun cfgC (cLv 1 3) (pcOf (lvAt 1 3)) 40
sym_block RLv14 := symRun cfgC (cLv 1 4) (pcOf (lvAt 1 4)) 40
sym_block RLv15 := symRun cfgC (cLv 1 5) (pcOf (lvAt 1 5)) 40
sym_block RLv16 := symRun cfgC (cLv 1 6) (pcOf (lvAt 1 6)) 40
sym_block RLv20 := symRun cfgC (cLv 2 0) (pcOf (lvAt 2 0)) 40
sym_block RLv21 := symRun cfgC (cLv 2 1) (pcOf (lvAt 2 1)) 40
sym_block RLv22 := symRun cfgC (cLv 2 2) (pcOf (lvAt 2 2)) 40
sym_block RLv23 := symRun cfgC (cLv 2 3) (pcOf (lvAt 2 3)) 40
sym_block RLv24 := symRun cfgC (cLv 2 4) (pcOf (lvAt 2 4)) 40
sym_block RLv25 := symRun cfgC (cLv 2 5) (pcOf (lvAt 2 5)) 40
sym_block RLv30 := symRun cfgC (cLv 3 0) (pcOf (lvAt 3 0)) 40
sym_block RLv31 := symRun cfgC (cLv 3 1) (pcOf (lvAt 3 1)) 40
sym_block RLv32 := symRun cfgC (cLv 3 2) (pcOf (lvAt 3 2)) 40
sym_block RLv33 := symRun cfgC (cLv 3 3) (pcOf (lvAt 3 3)) 40
sym_block RLv34 := symRun cfgC (cLv 3 4) (pcOf (lvAt 3 4)) 40
sym_block RLv35 := symRun cfgC (cLv 3 5) (pcOf (lvAt 3 5)) 40
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
def nbE (j : Nat) : E := .bin .xor (.bin .and (.bin .srl (.reg .x19) (.c (BitVec.ofNat 64 j))) (.c 1#64)) (.c 1#64)
def t6E (j : Nat) : E := .bin .add (.bin .sll (nbE j) (.c 4#64)) (.bin .sll (nbE j) (.c 5#64))
def pbE (j : Nat) : E := .un (.ld .bu j) (E.ld (.reg .x20))
def slotE (j : Nat) : E := .bin .sll (pbE j) (.c 4#64)
def a0E (j S : Nat) : E := .bin .add (t6E j) (.c (BitVec.ofNat 64 S))
def a1E (j D : Nat) : E := .bin .add (.bin .add (slotE j) (.c (BitVec.ofNat 64 D))) (t6E j)
def lvRegs (j S D : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (a0E j S)).set .x11
    (a1E j D)).set .x29 (a0E j S).ld).set .x30 (a0E j (S + 8)).ld
def lvMem (j S D : Nat) : SymMem :=
  [(⟨some (a1E j D), 8#64⟩, (a0E j (S + 8)).ld), (⟨some (a1E j D), 0#64⟩, (a0E j S).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩, (E.c (BitVec.ofNat 64 (S + 40))).ld),
   (⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvObl (j S D : Nat) : List Oblig :=
  [.valid ⟨some (a1E j D), 8#64⟩ 8, .valid ⟨some (a1E j D), 0#64⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 (S + 8)⟩ 8,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩,
   .ne ⟨some (t6E j), BitVec.ofNat 64 S⟩ ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩,
   .valid ⟨some (t6E j), BitVec.ofNat 64 S⟩ 8,
   .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 40)⟩ 8, .valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8,
   .align8 (.reg .x20), .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def lvSrc (lay j : Nat) : Nat :=
  0x310000 + 8136 + 64 * ((if lay = 1 then 66 else if lay = 2 then 116 else 165) + (if lay = 1 then 6 else 5) - j)
/-- Lower-layer path area in the final witness (pairing stage 1: abs `2904 + layerBase` = 15224 / 17872 / 20440). -/
def lvDst (lay : Nat) : Nat := 0x800 + (if lay = 1 then 13176 else if lay = 2 then 15824 else 18392)
def lvH (lay : Nat) : Nat := if lay = 1 then 7 else 6
def rLvs : List Result := [RLv10.res, RLv11.res, RLv12.res, RLv13.res, RLv14.res, RLv15.res, RLv16.res, RLv20.res,
  RLv21.res, RLv22.res, RLv23.res, RLv24.res, RLv25.res, RLv30.res, RLv31.res, RLv32.res, RLv33.res, RLv34.res,
  RLv35.res]
def rLv (lay j : Nat) : Result := rLvs.getD (lvIdx lay j) RLv10.res
theorem rLv_eq (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    rLv lay j = ⟨⟨lvRegs j (lvSrc lay j) (lvDst lay), lvMem j (lvSrc lay j) (lvDst lay),
      lvObl j (lvSrc lay j) (lvDst lay)⟩, .c (pcOf (lvAt lay j + 23)), .endOfCode, 23, 23⟩ := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
theorem run_lv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay - 1) :
    symRun cfgC (cLv lay j) (pcOf (lvAt lay j)) 40 = some (rLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
def LPLAN : Nat := 0xff9400
def LPlanAt (t : MachineState) : Prop :=
  ∀ k < 192, t.getMem (BitVec.ofNat 64 (LPLAN + 8 * k)) = bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * k)).take 8)
/-! ### C4: the top-path plan table of the expander's post-pass (data offset 26496 = legacy offset 2944) -/
/-- Line-A table (row `leaf % 64`, the six sibling slots of levels 0..5, stride 8) at `0xfffb80`. -/
def TOPA : Nat := 0xfffb80
/-- Line-B table (row `leaf / 64`, the six sibling slots of levels 6..11) at `0xfffd80`. -/
def TOPB : Nat := 0xfffd80
def topABytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 2944).take 512
def topBBytes : List (BitVec 8) := (SigGolfCandidate.T3M.Images.expandLegacyData.drop 3456).take 512
def TopTabAt (t : MachineState) : Prop :=
  (∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPA + 8 * k)) = bytesToWordLE ((topABytes.drop (8 * k)).take 8)) ∧
  ∀ k < 64, t.getMem (BitVec.ofNat 64 (TOPB + 8 * k)) = bytesToWordLE ((topBBytes.drop (8 * k)).take 8)
/-- Sibling slot (16-byte unit of the 48-slot top path area) of level `jj` in row `r` of line A (levels 0..5). -/
def slotA (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanA.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
/-- Sibling slot of level `jj + 6` in row `r` of line B. -/
def slotB (r jj : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.topPlanB.getD r []).getD jj 0 + 3 * (1 - r / 2 ^ jj % 2)
set_option maxRecDepth 100000 in
theorem topA_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topABytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotA r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem topB_ok : ∀ r < 64, ∀ jj < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((topBBytes.drop (8 * r)).take 8)) jj = BitVec.ofNat 64 (slotB r jj) := by
  decide +kernel
set_option maxRecDepth 100000 in
/-- Line A's sibling slots lie in `[24, 47]`, line B's in `[0, 23]`; within a line they are pairwise distinct. -/
theorem slots_ok : (∀ r < 64, ∀ i < 6, 24 ≤ slotA r i ∧ slotA r i ≤ 47) ∧ (∀ r < 64, ∀ i < 6, slotB r i ≤ 23) ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotA r i = slotA r i' → i = i') ∧
    (∀ r < 64, ∀ i < 6, ∀ i' < 6, slotB r i = slotB r i' → i = i') := by
  decide +kernel
def lvRow (lay r : Nat) : Nat := if lay = 1 then 64 + r else r
set_option maxRecDepth 100000 in
theorem lplan1_ok : ∀ r < 128, ∀ j < 7,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * (64 + r))).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lplan2_ok : ∀ r < 64, ∀ j < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * r)).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0) ∧
    (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 3 r).getD j 0 = (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lowerPlan_lt : (∀ r < 128, ∀ j < 7, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 1 r).getD j 0 + 4 ≤ 25) ∧
    (∀ r < 64, ∀ j < 6, (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan 2 r).getD j 0 + 4 ≤ 20) := by
  decide +kernel
def plan (lay r j : Nat) : Nat := (ClaudeWCT.W9.Machine.Expand.OldW.lowerPlan (Fin.ofNat 4 lay) r).getD j 0
theorem plan_ok (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * lvRow lay r)).take 8)) j =
      BitVec.ofNat 64 (plan lay r j) ∧ plan lay r j + 4 ≤ (if lay = 1 then 25 else 20) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hr hj
  unfold plan lvRow
  interval_cases lay
  · simp only [if_true] at hr hj ⊢
    exact ⟨lplan1_ok r (by omega) j hj, lowerPlan_lt.1 r (by omega) j hj⟩
  · simp only [show (2 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
  · simp only [show (3 : Nat) ≠ 1 by decide, if_false] at hr hj ⊢
    rw [show (Fin.ofNat 4 3 : SigGolfCandidate.T3.Layer) = 3 from rfl, (lplan2_ok r (by omega) j hj).2]
    exact ⟨(lplan2_ok r (by omega) j hj).1, lowerPlan_lt.2 r (by omega) j hj⟩
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
theorem nbE_eval (j : Nat) (hj : j < 7) : (nbE j).eval s = BitVec.ofNat 64 (1 - r / 2 ^ j % 2) := by
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  apply BitVec.eq_of_toNat_eq
  simp only [nbE, E.eval, BinOp.eval, h19, BitVec.toNat_xor, BitVec.toNat_and, BitVec.toNat_ushiftRight,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show r < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show j < 64 by omega), show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.and_one_is_mod]
  rcases (show r / 2 ^ j % 2 = 0 ∨ r / 2 ^ j % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
theorem t6E_eval (j : Nat) (hj : j < 7) : (t6E j).eval s = BitVec.ofNat 64 (48 * (1 - r / 2 ^ j % 2)) := by
  have hb := nbE_eval h19 hr j hj
  simp only [t6E, E.eval, BinOp.eval, hb]
  have : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases (show r / 2 ^ j % 2 = 0 ∨ r / 2 ^ j % 2 = 1 by omega) with h | h <;> rw [h] <;> decide
end eval
theorem pbE_eval {s : MachineState} {lay r : Nat} (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) (j : Nat) (hj : j < lvH lay) :
    (pbE j).eval s = BitVec.ofNat 64 (plan lay r j) := by
  have hrow : lvRow lay r < 192 := by
    unfold lvRow lvH at *; split <;> simp_all <;> omega
  simp only [pbE, E.eval, UnOp.eval, h20]
  rw [hp _ hrow, (plan_ok lay r j hl hr hj).1]
theorem lvH_le (lay : Nat) : lvH lay ≤ 7 := by unfold lvH; split <;> omega
theorem valid8 (X : Nat) (h : X + 8 ≤ 16777216) (h8 : X % 8 = 0) : accessValid (BitVec.ofNat 64 X) 8 = true := by
  rw [accessValid_iff, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact ⟨by rw [show MEMORY_BYTES = 16777216 from rfl]; omega, h8⟩
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lv_spec (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj' : j + 1 < lvH lay) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay j)) (r : Nat) (hr : r < 2 ^ lvH lay) (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 23 23 t ∧ t.pc = pcOf (lvAt lay j + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay j + 48 * (1 - r / 2 ^ j % 2)))
        else if A = lvDst lay + 16 * plan lay r j + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 40))
        else if A = lvDst lay + 16 * plan lay r j + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay j + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hj : j < lvH lay := by omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : j < 7 := by omega
  have ht6 := t6E_eval h19 hr7 j hj7
  have hpb := pbE_eval hl hr h20 hp j hj
  have hpl := (plan_ok lay r j hl hr hj).2
  have hpl23 : plan lay r j ≤ 23 := by split_ifs at hpl <;> omega
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hD : lvDst lay + 16 * 23 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst; split_ifs <;> omega
  have hDp : lvDst lay + 16 * plan lay r j + 64 ≤ 0x800 + 20912 := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
  have hS16 : lvSrc lay j % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  have hrun := run_lv lay j ⟨h1, h4⟩ (by omega)
  rw [rLv_eq lay j ⟨h1, h4⟩ (by omega)] at hrun
  have hslot : (slotE j).eval s = BitVec.ofNat 64 (16 * plan lay r j) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  have ha0 : ∀ S, (a0E j S).eval s = BitVec.ofNat 64 (48 * (1 - r / 2 ^ j % 2) + S) := fun S => by
    simp only [a0E, E.eval, BinOp.eval, ht6, ofNat_add_ofNat]
  have ha1 : (a1E j (lvDst lay)).eval s =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)) := by
    simp only [a1E, E.eval, BinOp.eval, hslot, ht6, ofNat_add_ofNat]; congr 1; ring
  have hobl : Oblig.all s (lvObl j (lvSrc lay j) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ha1, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, hslot, ofNat_add_ofNat]
      intro h; have := (ofNat_inj (by omega) (by omega)).mp h; omega
    · simp only [Oblig.holds, Addr.eval, ht6, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  refine ⟨_, symRun_sound hrun (Compact2.code_cLv hc lay j ⟨h1, h4⟩ hj) s hpc hobl, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    rw [Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    simp only [Result.toState_getMem, lvMem, memEval_cons, memEval_nil, Addr.eval, E.eval, ha0, ha1, hslot,
      ofNat_add_ofNat, BitVec.add_zero]
    have e1 : 48 * (1 - r / 2 ^ j % 2) + (lvSrc lay j + 8) = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) + 8 := by ring
    have e2 : 48 * (1 - r / 2 ^ j % 2) + lvSrc lay j = lvSrc lay j + 48 * (1 - r / 2 ^ j % 2) := by ring
    have e3 : 16 * plan lay r j + (lvDst lay + 40) = lvDst lay + 16 * plan lay r j + 40 := by ring
    have e4 : 16 * plan lay r j + (lvDst lay + 32) = lvDst lay + 16 * plan lay r j + 32 := by ring
    rw [e1, e2, e3, e4]
    by_cases q1 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2) + 8
    · subst q1; simp
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h)), if_neg q1]
      by_cases q2 : A = lvDst lay + 16 * plan lay r j + 48 * (1 - r / 2 ^ j % 2)
      · subst q2; simp
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), if_neg q2]
        by_cases q3 : A = lvDst lay + 16 * plan lay r j + 40
        · subst q3; simp
        · rw [if_neg (fun h => q3 ((ofNat_inj hA (by omega)).mp h)), if_neg q3]
          by_cases q4 : A = lvDst lay + 16 * plan lay r j + 32
          · subst q4; simp
          · rw [if_neg (fun h => q4 ((ofNat_inj hA (by omega)).mp h)), if_neg q4]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
sym_block RLvA1 := symRun cfgC (cLvA 1) (pcOf (lvAt 1 (rootJ 1))) 40
sym_block RLvA2 := symRun cfgC (cLvA 2) (pcOf (lvAt 2 (rootJ 2))) 40
sym_block RLvA3 := symRun cfgC (cLvA 3) (pcOf (lvAt 3 (rootJ 3))) 40
sym_block RRT1 := symRun cfgC (cRT 1) (pcOf (rtAt 1)) 40
sym_block RRT2 := symRun cfgC (cRT 2) (pcOf (rtAt 2)) 40
sym_block RRT3 := symRun cfgC (cRT 3) (pcOf (rtAt 3)) 40
sym_block RLvB1 := symRun cfgC (cLvB 1) (pcOf (lvAt 1 (rootJ 1) + 11)) 40
sym_block RLvB2 := symRun cfgC (cLvB 2) (pcOf (lvAt 2 (rootJ 2) + 11)) 40
sym_block RLvB3 := symRun cfgC (cLvB 3) (pcOf (lvAt 3 (rootJ 3) + 11)) 40
def lvARegs (j S D : Nat) : RegFile :=
  ((((RegFile.init.set .x6 (slotE j)).set .x10 (.c (BitVec.ofNat 64 S))).set .x11
    (.bin .add (slotE j) (.c (BitVec.ofNat 64 D)))).set .x29 (E.c (BitVec.ofNat 64 (S + 32))).ld).set .x30
    (E.c (BitVec.ofNat 64 (S + 40))).ld
def lvAMem (j S D : Nat) : SymMem :=
  [(⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩, (E.c (BitVec.ofNat 64 (S + 32))).ld)]
def lvAObl (j D : Nat) : List Oblig :=
  [.valid ⟨some (slotE j), BitVec.ofNat 64 (D + 32)⟩ 8, .align8 (.reg .x20),
   .valid ⟨some (.reg .x20), BitVec.ofNat 64 j⟩ 1]
def rtRegs : RegFile := RegFile.init.set .x29 (.c 1#64)
def rtMem : SymMem := [(⟨some (.reg .x11), 24#64⟩, .c 1#64), (⟨some (.reg .x11), 40#64⟩, .reg .x30)]
def rtObl : List Oblig := [.valid ⟨some (.reg .x11), 24#64⟩ 8, .valid ⟨some (.reg .x11), 40#64⟩ 8]
def aBE (j : Nat) : E := .bin .add (.reg .x10) (t6E j)
def dBE (j : Nat) : E := .bin .add (.reg .x11) (t6E j)
def lvBRegs (j : Nat) : RegFile :=
  (((((RegFile.init.set .x6 (t6E j)).set .x7 (.bin .sll (nbE j) (.c 5#64))).set .x10 (aBE j)).set .x11
    (dBE j)).set .x29 (aBE j).ld).set .x30 (E.bin .add (aBE j) (.c 8#64)).ld
def lvBMem (j : Nat) : SymMem :=
  [(⟨some (dBE j), 8#64⟩, (E.bin .add (aBE j) (.c 8#64)).ld), (⟨some (dBE j), 0#64⟩, (aBE j).ld)]
def lvBObl (j : Nat) : List Oblig :=
  [.valid ⟨some (dBE j), 8#64⟩ 8, .valid ⟨some (dBE j), 0#64⟩ 8, .valid ⟨some (aBE j), 8#64⟩ 8,
   .valid ⟨some (aBE j), 0#64⟩ 8]
def rLvA (lay : Nat) : Result := [RLvA1.res, RLvA2.res, RLvA3.res].getD (lay - 1) RLvA1.res
def rRT (lay : Nat) : Result := [RRT1.res, RRT2.res, RRT3.res].getD (lay - 1) RRT1.res
def rLvB (lay : Nat) : Result := [RLvB1.res, RLvB2.res, RLvB3.res].getD (lay - 1) RLvB1.res
theorem rLvA_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvA lay = ⟨⟨lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay),
      lvAMem (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay), lvAObl (rootJ lay) (lvDst lay)⟩,
      .c (pcOf (rtAt lay)), .jump, 11, 11⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvA lay) (pcOf (lvAt lay (rootJ lay))) 40 = some (rLvA lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem rRT_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rRT lay = ⟨⟨rtRegs, rtMem, rtObl⟩, .c (pcOf (lvAt lay (rootJ lay) + 11)), .jump, 4, 4⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_rt (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cRT lay) (pcOf (rtAt lay)) 40 = some (rRT lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem rLvB_eq (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    rLvB lay = ⟨⟨lvBRegs (rootJ lay), lvBMem (rootJ lay), lvBObl (rootJ lay)⟩,
      .c (pcOf (lvAt lay (rootJ lay) + 23)), .endOfCode, 12, 12⟩ := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
theorem run_lvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    symRun cfgC (cLvB lay) (pcOf (lvAt lay (rootJ lay) + 11)) 40 = some (rLvB lay) := by
  obtain ⟨h1, h4⟩ := hl; interval_cases lay <;> kernel_rfl
section
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.CompactCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
/-- C3 (FULL, E6): the root level (`j = rootJ lay`) copies like any other level and also writes LE64(1) at
window + 24, the encoding row tweak's high word (27 steps: the trampoline adds 4). -/
theorem lvRoot_spec (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) (s : MachineState)
    (hpc : s.pc = pcOf (lvAt lay (rootJ lay))) (r : Nat) (hr : r < 2 ^ lvH lay)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 r)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 (LPLAN + 8 * lvRow lay r)) (hp : LPlanAt s) :
    ∃ t, Steps im s 27 27 t ∧ t.pc = pcOf (lvAt lay (rootJ lay) + 23) ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x29, .x30] ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
        else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then
          s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
        else s.getMem (BitVec.ofNat 64 A) := by
  have hM : MEMORY_BYTES = 16777216 := rfl
  have hjl : rootJ lay < lvH lay := by obtain ⟨h1, h4⟩ := hl; unfold rootJ lvH; split_ifs <;> omega
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : rootJ lay < 7 := by omega
  have hpb := pbE_eval hl hr h20 hp (rootJ lay) hjl
  have hpl := (plan_ok lay r (rootJ lay) hl hr hjl).2
  have hb : r / 2 ^ rootJ lay % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hDp : lvDst lay + 16 * plan lay r (rootJ lay) + 64 ≤ 0x800 + 20912 ∧ 0x800 + 11648 ≤ lvDst lay := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x310000 + 8136 + 64 * 66 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x310000 + 21832 := by
    unfold lvSrc; unfold lvH at hjl; split_ifs at * <;> omega
  have hS16 : lvSrc lay (rootJ lay) % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 8 = 0 := by unfold lvDst; split_ifs <;> omega
  -- abbreviations
  have hslot : (slotE (rootJ lay)).eval s = BitVec.ofNat 64 (16 * plan lay r (rootJ lay)) := by
    simp only [slotE, E.eval, BinOp.eval, hpb]
    rw [show (4#64 : Word).toNat % 64 = 4 from rfl, ofNat_shl]; congr 1; ring
  -- piece A: Z low word, then `jal` to the trampoline
  have hrunA := run_lvA lay ⟨h1, h4⟩
  rw [rLvA_eq lay ⟨h1, h4⟩] at hrunA
  have hoblA : Oblig.all s (lvAObl (rootJ lay) (lvDst lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvAObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hslot, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, E.eval, h20, BitVec.toNat_ofNat]; unfold LPLAN; omega
    · simp only [Oblig.holds, Addr.eval, E.eval, h20, ofNat_add_ofNat, accessValid_iff, BitVec.toNat_ofNat]
      unfold LPLAN lvRow at *; split_ifs <;> omega
  have sA := symRun_sound hrunA (code_cLvA hc lay ⟨h1, h4⟩) s hpc hoblA
  generalize ht1 : Result.toState _ s = t1 at sA
  have p1 : t1.pc = pcOf (rtAt lay) := by rw [← ht1]; simp [Result.toState_pc, E.eval]
  have ga : ∀ x : Reg, t1.getReg x = ((lvARegs (rootJ lay) (lvSrc lay (rootJ lay)) (lvDst lay)).get x).eval s := by
    intro x; rw [← ht1, Result.toState_getReg]
  have a11 : t1.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval, BinOp.eval, hslot, ofNat_add_ofNat]
    congr 1; ring
  have a10 : t1.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have a30 : t1.getReg .x30 = s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40)) := by
    rw [ga]; simp only [lvARegs, RegFile.set, RegFile.get, E.eval]
  have aR : RegsExcept s t1 [.x6, .x10, .x11, .x29, .x30] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h10, h11, h29, h30⟩ := hx
    rw [ga]
    cases x <;> first | rfl | (exfalso; simp_all)
  have am : ∀ A < 2 ^ 64, t1.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 32 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 32))
      else s.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht1]
    simp only [Result.toState_getMem, lvAMem, memEval_cons, memEval_nil, Addr.eval, E.eval, hslot, ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 32
    · subst q; rw [if_pos (by congr 1; ring), if_pos rfl]
    · rw [if_neg (fun h => q (by have := (ofNat_inj hA (by omega)).mp h; omega)), if_neg q]
  -- piece B: the trampoline
  have hrunR := run_rt lay ⟨h1, h4⟩
  rw [rRT_eq lay ⟨h1, h4⟩] at hrunR
  have hoblR : Oblig.all t1 rtObl := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [rtObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, E.eval, a11, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
  have sR := symRun_sound hrunR (code_cRT hc lay ⟨h1, h4⟩) t1 p1 hoblR
  generalize ht2 : Result.toState _ t1 = t2 at sR
  have p2 : t2.pc = pcOf (lvAt lay (rootJ lay) + 11) := by rw [← ht2]; simp [Result.toState_pc, E.eval]
  have bR : RegsExcept t1 t2 [.x29] := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [← ht2, Result.toState_getReg]
    cases x <;> first | rfl | (exfalso; simp_all)
  have bm : ∀ A < 2 ^ 64, t2.getMem (BitVec.ofNat 64 A) =
      if A = lvDst lay + 16 * plan lay r (rootJ lay) + 24 then 1#64
      else if A = lvDst lay + 16 * plan lay r (rootJ lay) + 40 then s.getMem (BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 40))
      else t1.getMem (BitVec.ofNat 64 A) := by
    intro A hA
    rw [← ht2]
    simp only [Result.toState_getMem, rtMem, memEval_cons, memEval_nil, Addr.eval, E.eval, a11, a30,
      ofNat_add_ofNat]
    by_cases q : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
    · subst q; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => q ((ofNat_inj hA (by omega)).mp h)), if_neg q]
      by_cases q' : A = lvDst lay + 16 * plan lay r (rootJ lay) + 40
      · subst q'; rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun h => q' ((ofNat_inj hA (by omega)).mp h)), if_neg q']
  -- piece C: the sibling copy
  have hrunB := run_lvB lay ⟨h1, h4⟩
  rw [rLvB_eq lay ⟨h1, h4⟩] at hrunB
  have h19' : t2.getReg .x19 = BitVec.ofNat 64 r := by
    rw [bR.get (by decide), aR.get (by decide), h19]
  have ht6 := t6E_eval h19' hr7 (rootJ lay) hj7
  have b10 : t2.getReg .x10 = BitVec.ofNat 64 (lvSrc lay (rootJ lay)) := by rw [bR.get (by decide), a10]
  have b11 : t2.getReg .x11 = BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay)) := by
    rw [bR.get (by decide), a11]
  have haB : (aBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvSrc lay (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [aBE, E.eval, BinOp.eval, b10, ht6, ofNat_add_ofNat]
  have hdB : (dBE (rootJ lay)).eval t2 =
      BitVec.ofNat 64 (lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)) := by
    simp only [dBE, E.eval, BinOp.eval, b11, ht6, ofNat_add_ofNat]
  have hoblB : Oblig.all t2 (lvBObl (rootJ lay)) := by
    rw [Oblig.all_iff]
    intro o ho
    simp only [lvBObl, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, hdB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat]; exact valid8 _ (by omega) (by omega)
    · simp only [Oblig.holds, Addr.eval, haB, ofNat_add_ofNat, BitVec.add_zero]; exact valid8 _ (by omega) (by omega)
  have sB := symRun_sound hrunB (code_cLvB hc lay ⟨h1, h4⟩) t2 p2 hoblB
  generalize ht3 : Result.toState _ t2 = t3 at sB
  refine ⟨t3, ((sA.trans sR).trans sB).of_eq (by norm_num) (by norm_num), ?_, ?_, ?_⟩
  · rw [← ht3]; simp [Result.toState_pc, E.eval]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h6, h7, h10, h11, h29, h30⟩ := hx
    have e2 : t2.getReg x = s.getReg x := by
      rw [bR.get (by simp [h29]), aR.get (by simp [h6, h10, h11, h29, h30])]
    rw [← ht3, Result.toState_getReg, ← e2]
    cases x <;> first | rfl | (exfalso; simp_all)
  · intro A hA
    rw [← ht3]
    simp only [Result.toState_getMem, lvBMem, memEval_cons, memEval_nil, Addr.eval, E.eval, BinOp.eval, haB, hdB,
      ofNat_add_ofNat, BitVec.add_zero]
    have hsrc : ∀ X, lvSrc lay (rootJ lay) ≤ X → X < lvSrc lay (rootJ lay) + 64 →
        t2.getMem (BitVec.ofNat 64 X) = s.getMem (BitVec.ofNat 64 X) := by
      intro X hX1 hX2
      rw [bm X (by omega), if_neg (by omega), if_neg (by omega), am X (by omega), if_neg (by omega)]
    rw [hsrc _ (by omega) (by omega), hsrc _ (by omega) (by omega)]
    by_cases q1 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2) + 8
    · subst q1
      rw [if_pos rfl, if_neg (by omega), if_pos rfl]
    · rw [if_neg (fun h => q1 ((ofNat_inj hA (by omega)).mp h))]
      by_cases q2 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 48 * (1 - r / 2 ^ rootJ lay % 2)
      · subst q2
        rw [if_pos rfl, if_neg (by omega), if_neg q1, if_pos rfl]
      · rw [if_neg (fun h => q2 ((ofNat_inj hA (by omega)).mp h)), bm A hA, am A hA]
        by_cases q3 : A = lvDst lay + 16 * plan lay r (rootJ lay) + 24
        · rw [if_pos q3, if_pos q3]
        · rw [if_neg q3, if_neg q3, if_neg q1, if_neg q2]
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
