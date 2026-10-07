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
theorem hookCode_at : CodeAt image (pcOf 1117) hookCode :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block hookCodeBlock := symRun { noAlias := true } hookCode (pcOf 1117) 30
def testCode : List (BitVec 32) := [0x41478e33,0xfffe0e13]
theorem testCode_at : CodeAt image (pcOf 40875) testCode :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block testCodeBlock := symRun { noAlias := true } testCode (pcOf 40875) 30
def branch1Code : List (BitVec 32) := [34479715]
theorem branch1Code_at : CodeAt image (pcOf 40877) branch1Code :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
def branch2Code : List (BitVec 32) := [33819747]
theorem branch2Code_at : CodeAt image (pcOf 40878) branch2Code :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
def pairCode : List (BitVec 32) := [134967,638521107,134839,537824915,963331,9352067,7286819,8336419,51294979,59683715,40843299,41892899,32871]
theorem pairCode_at : CodeAt image (pcOf 40879) pairCode :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block pairCodeBlock := symRun { noAlias := true } pairCode (pcOf 40879) 30
def backCode : List (BitVec 32) := [0xa8cd906f]
theorem backCode_at : CodeAt image (pcOf 40892) backCode :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block backCodeBlock := symRun { noAlias := true } backCode (pcOf 40892) 30
def selectCode : List (BitVec 32) := testCode ++ branch1Code
theorem selectCode_at : CodeAt image (pcOf 40875) selectCode :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block selectBlock := symRun { noAlias := true } selectCode (pcOf 40875) 30
sym_block layerBranch := symRun { noAlias := true } branch2Code (pcOf 40878) 30
theorem pair_spec (s : MachineState) (hpc : s.pc = pcOf 40879) (ret : Nat)
    (h1 : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 13 13 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  have hobl : Oblig.all s pairCodeBlock.res.st.obl := by
    simp [pairCodeBlock.res, rv_simp]
  refine ⟨_, symRun_sound pairCodeBlock pairCode_at s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
def remaining (s : MachineState) : Word := s.getReg .x15 - s.getReg .x20 - 1
theorem select_spec (s : MachineState) (hpc : s.pc = pcOf 40875) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if remaining s = 0 then pcOf 40878 else pcOf 40892) ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound selectBlock selectCode_at s hpc (by simp [selectBlock.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · simp [Result.toState_getReg, selectBlock.res, rv_simp, remaining, sub_eq_add_neg]
  · intro r hr; simp at hr; cases r <;> simp_all [selectBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, selectBlock.res, rv_simp]
theorem layer_spec (s : MachineState) (hpc : s.pc = pcOf 40878) :
    ∃ t, Steps image s 1 1 t ∧
      t.pc = (if s.getReg .x8 = 0 then pcOf 40892 else pcOf 40879) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound layerBranch branch2Code_at s hpc (by simp [layerBranch.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, layerBranch.res, rv_simp]
  · intro r hr; cases r <;> simp [layerBranch.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, layerBranch.res, rv_simp]
theorem hook_spec (s : MachineState) (hpc : s.pc = pcOf 1117) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 40875 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound hookCodeBlock hookCode_at s hpc (by simp [hookCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, hookCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [hookCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, hookCodeBlock.res, rv_simp]
theorem back_spec (s : MachineState) (hpc : s.pc = pcOf 40892) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1119 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound backCodeBlock backCode_at s hpc (by simp [backCodeBlock.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, backCodeBlock.res, rv_simp, pcOf]
  · intro r hr; cases r <;> simp [backCodeBlock.res, rv_simp]; rfl
  · intro A hA hn; simp [Result.toState_getMem, backCodeBlock.res, rv_simp]
theorem continue_spec (s : MachineState) (hpc : s.pc = pcOf 1117)
    (hc : remaining s ≠ 0 ∨ s.getReg .x8 = 0) :
    ∃ t k, Steps image s k k t ∧ k ≤ 6 ∧ t.pc = pcOf 1119 ∧
      t.getReg .x28 = remaining s ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec s hpc
  have he : remaining u = remaining s := by
    unfold remaining
    rw [ur.get (by simp), ur.get (by simp)]
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec u up
  rw [he] at vp v28
  by_cases hz : remaining s = 0
  · rw [if_pos hz] at vp
    have h8 : v.getReg .x8 = 0 := by
      rw [vr.get (by simp), ur.get (by simp)]
      exact hc.resolve_left (not_not_intro hz)
    obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec v vp
    rw [if_pos h8] at wp
    obtain ⟨t, wt, tp, tr, tf⟩ := back_spec w wp
    refine ⟨t, 6, ((su.trans uv).trans vw).trans wt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), wr.get (by simp), v28]
    · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
    · exact (((uf.trans vf).trans wf).trans tf).mono (by intro A hA h; simpa using h)
  · rw [if_neg hz] at vp
    obtain ⟨t, vt, tp, tr, tf⟩ := back_spec v vp
    refine ⟨t, 5, (su.trans uv).trans vt, by omega, tp, ?_, ?_, ?_⟩
    · rw [tr.get (by simp), v28]
    · exact ((ur.trans vr).trans tr).mono (by decide)
    · exact ((uf.trans vf).trans tf).mono (by intro A hA h; simpa using h)
theorem finish_spec (s : MachineState) (hpc : s.pc = pcOf 1117) (ret : Nat)
    (hz : remaining s = 0) (hl : s.getReg .x8 ≠ 0) (hra : s.getReg .x1 = pcOf ret) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NODE) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NODE + 8)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 48)) = s.getMem (BitVec.ofNat 64 (NODE + 48)) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 56)) = s.getMem (BitVec.ofNat 64 (NODE + 56)) ∧
      RegsExcept s t [.x6, .x7, .x28, .x29, .x30] ∧
      Frame s t (fun A => A = ENC ∨ A = ENC + 8 ∨ A = ENC + 48 ∨ A = ENC + 56) := by
  obtain ⟨u, su, up, ur, uf⟩ := hook_spec s hpc
  have he : remaining u = 0 := by unfold remaining; rw [ur.get (by simp), ur.get (by simp)]; exact hz
  obtain ⟨v, uv, vp, v28, vr, vf⟩ := select_spec u up
  rw [if_pos he] at vp
  have h8 : v.getReg .x8 ≠ 0 := by rw [vr.get (by simp), ur.get (by simp)]; exact hl
  obtain ⟨w, vw, wp, wr, wf⟩ := layer_spec v vp
  rw [if_neg h8] at wp
  obtain ⟨t, wt, tp, m0, m8, m48, m56, tr, tf⟩ := pair_spec w wp ret
    (by rw [wr.get (by simp), vr.get (by simp), ur.get (by simp)]; exact hra)
  have fsw : Frame s w (fun _ => False) := ((uf.trans vf).trans wf).mono (by intro A hA h; simpa using h)
  refine ⟨t, ((su.trans uv).trans vw).trans wt, tp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m0, fsw.get (by decide) (by simp)]
  · rw [m8, fsw.get (by decide) (by simp)]
  · rw [m48, fsw.get (by decide) (by simp)]
  · rw [m56, fsw.get (by decide) (by simp)]
  · exact (((ur.trans vr).trans wr).trans tr).mono (by decide)
  · exact (fsw.trans tf).mono (by intro A hA h; simpa using h)
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
theorem e_hdrA_at : CodeAt image (pcOf 1119) e_hdrA :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hdrA := symRun { noAlias := true } e_hdrA (pcOf 1119) 30
def e_hdrB : List (BitVec 32) := [426899,67109651,33817187]
theorem e_hdrB_at : CodeAt image (pcOf 42765) e_hdrB :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hdrB := symRun { noAlias := true } e_hdrB (pcOf 42765) 30
def e_hdrC : List (BitVec 32) := [17077011,538141459,0xfff40f13,51322643,31679283,0xc100f13,59711251,31679283,0xd44d706f]
theorem e_hdrC_at : CodeAt image (pcOf 42768) e_hdrC :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hdrC := symRun { noAlias := true } e_hdrC (pcOf 42768) 30
def e_hdrD : List (BitVec 32) := [0xd44d706f]
theorem e_hdrD_at : CodeAt image (pcOf 42776) e_hdrD :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hdrD := symRun { noAlias := true } e_hdrD (pcOf 42776) 30
def e_hdrE : List (BitVec 32) := [134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
theorem e_hdrE_at : CodeAt image (pcOf 1129) e_hdrE :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hdrE := symRun { noAlias := true } e_hdrE (pcOf 1129) 30
def e_hpA : List (BitVec 32) := [0xf49333,19071795,16978707,538141459,50601747,31679283,0xc100f13,59711251,31679283,134711,0x600e0e13,7223331,932899,267875]
theorem e_hpA_at : CodeAt image (pcOf 42741) e_hpA :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hpA := symRun { noAlias := true } e_hpA (pcOf 42741) 30
def e_hpZ : List (BitVec 32) := [929827,930851,0xbb0d706f]
theorem e_hpZ_at : CodeAt image (pcOf 42755) e_hpZ :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hpZ := symRun { noAlias := true } e_hpZ (pcOf 42755) 30
def e_hpJ : List (BitVec 32) := [0xbb0d706f]
theorem e_hpJ_at : CodeAt image (pcOf 42757) e_hpJ :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_hpJ := symRun { noAlias := true } e_hpJ (pcOf 42757) 30
def e_w1009 : List (BitVec 32) := [2451]
theorem e_w1009_at : CodeAt image (pcOf 1009) e_w1009 :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_w1009 := symRun { noAlias := true } e_w1009 (pcOf 1009) 30
def e_slA : List (BitVec 32) := [4824595,264291]
theorem e_slA_at : CodeAt image (pcOf 42758) e_slA :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_slA := symRun { noAlias := true } e_slA (pcOf 42758) 30
def e_slB : List (BitVec 32) := [624739]
theorem e_slB_at : CodeAt image (pcOf 42760) e_slB :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_slB := symRun { noAlias := true } e_slB (pcOf 42760) 30
def e_slN : List (BitVec 32) := [17698323,0xc48d706f]
theorem e_slN_at : CodeAt image (pcOf 42761) e_slN :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_slN := symRun { noAlias := true } e_slN (pcOf 42761) 30
def e_slT : List (BitVec 32) := [34475539,0xc40d706f]
theorem e_slT_at : CodeAt image (pcOf 42763) e_slT :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_slT := symRun { noAlias := true } e_slT (pcOf 42763) 30
def e_slZ : List (BitVec 32) := [0xc40d706f]
theorem e_slZ_at : CodeAt image (pcOf 42764) e_slZ :=
  codeAt_expand_slice (by decide +kernel) (by decide +kernel)
sym_block eb_slZ := symRun { noAlias := true } e_slZ (pcOf 42764) 30
def slotOff (lay : T3.Layer) (c : Nat) : Nat := if lay = 0 then 16 * c + 32 else if c = 0 then 0 else 16 * c + 16
def hpK (lay : T3.Layer) : Nat := if lay = 0 then 19 else 17
def slK (lay : T3.Layer) (i : Nat) : Nat := if lay = 0 then 5 else if i = 0 then 5 else 6
def hdrK (lay : Nat) : Nat := if lay = 0 then 19 else 27
section blocks
variable (s : MachineState)
theorem rl997_spec (hpc : s.pc = pcOf 997) (lay : T3.Layer) (tree leaf : Nat)
    (hr : tree * 2 ^ T3.height lay + leaf < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 (T3.height lay)) :
    ∃ t, Steps image s (hpK lay) (hpK lay) t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x30] ∧
      Frame s t (fun A => A = LEAFPK ∨ A = LEAFPK + 8 ∨ A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 42741 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_997 codeAt_997 s hpc (by simp [eblk_997.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_997.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g9 : t1.getReg .x9 = BitVec.ofNat 64 tree := by rw [r1.get (by decide), h9]
  have g18 : t1.getReg .x18 = BitVec.ofNat 64 leaf := by rw [r1.get (by decide), h18]
  have g15 : t1.getReg .x15 = BitVec.ofNat 64 (T3.height lay) := by rw [r1.get (by decide), h15]
  obtain ⟨t2, s2, p2, m16, m24, x28, r2, f2⟩ : ∃ t, Steps image t1 14 14 t ∧
      t.pc = (if lay = 0 then pcOf 42755 else pcOf 42757) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 16)) = T3.hyperWord lay.val (tree * 2 ^ T3.height lay + leaf) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + 24)) = 0 ∧ t.getReg .x28 = BitVec.ofNat 64 LEAFPK ∧
      RegsExcept t1 t [.x6, .x28, .x30] ∧ Frame t1 t (fun A => A = LEAFPK + 16 ∨ A = LEAFPK + 24) := by
    refine ⟨_, symRun_sound eb_hpA e_hpA_at t1 p1
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
  obtain ⟨t3, s3, p3, z0, r3, f3⟩ : ∃ t, Steps image t2 (if lay = 0 then 3 else 1) (if lay = 0 then 3 else 1) t ∧
      t.pc = pcOf 1009 ∧
      (lay = 0 → t.getMem (BitVec.ofNat 64 LEAFPK) = 0 ∧ t.getMem (BitVec.ofNat 64 (LEAFPK + 8)) = 0) ∧
      RegsExcept t2 t [] ∧ Frame t2 t (fun A => A = LEAFPK ∨ A = LEAFPK + 8) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      refine ⟨_, (symRun_sound eb_hpZ e_hpZ_at t2 p2
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
      refine ⟨_, (symRun_sound eb_hpJ e_hpJ_at t2 p2 (by simp [eb_hpJ.res, rv_simp])).of_eq (by simp [h0, eb_hpJ.res])
        (by simp [h0, eb_hpJ.res]), ?_, fun h => absurd h h0, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hpJ.res, E.eval]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
  obtain ⟨t4, s4, p4, x19, r4, f4⟩ : ∃ t, Steps image t3 1 1 t ∧ t.pc = pcOf 1010 ∧
      t.getReg .x19 = BitVec.ofNat 64 0 ∧ RegsExcept t3 t [.x19] ∧ Frame t3 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_w1009 e_w1009_at t3 p3 (by simp [eb_w1009.res, rv_simp]), ?_, ?_, ?_, ?_⟩
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
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if n ≤ i then pcOf 1063 else pcOf 1011) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1010 codeAt_1010 s hpc (by simp [eblk_1010.res, rv_simp]), ?_, ?_, ?_⟩
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
    ∃ t, Steps image s 16 16 t ∧ t.pc = pcOf 1027 ∧
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
  refine ⟨_, symRun_sound eblk_1011 codeAt_1011 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
theorem lbu_word1027 : decodeInstruction (0x000e4a03 : BitVec 32) = some (.base (.LBU .x20 .x28 0)) := rfl
theorem rl1027_spec (hpc : s.pc = pcOf 1027) (i d : Nat) (hi : i < 64) (hd : d < 256)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (i + DIGITS))
    (hb : s.getByte (BitVec.ofNat 64 (DIGITS + i)) = BitVec.ofNat 8 d) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1028 ∧ t.getReg .x20 = BitVec.ofNat 64 d ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  have ea : s.getReg .x28 + signExtend12 0 = BitVec.ofNat 64 (DIGITS + i) := by
    rw [h28, show signExtend12 (0 : BitVec 12) = 0 from rfl, add_zero, Nat.add_comm]
  have hv : accessValid (s.getReg .x28 + signExtend12 0) 1 = true := by
    rw [ea, accessValid_iff, toNat_ofNat_lt (by simp only [DIGITS]; omega)]; simp only [MEMORY_BYTES, DIGITS]; omega
  refine ⟨_, steps_lbu codeAt_1027 hpc lbu_word1027 hv, ?_, ?_, ?_, ?_⟩
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
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if lay = 0 then pcOf 1030 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 7 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  have hz : (BitVec.ofNat 64 lay = 0#64) ↔ lay = 0 := by
    constructor
    · intro e
      have q := congrArg BitVec.toNat e
      simpa [toNat_ofNat_lt hlay] using q
    · intro e; subst lay; rfl
  refine ⟨_, symRun_sound eblk_1028 codeAt_1028 s hpc (by simp [eblk_1028.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1028.res, E.eval, CmpOp.eval, h8, hz]
  · simp [eblk_1028.res, rv_simp]
  · ex_regs eblk_1028.res
  · intro A _ _; simp [eblk_1028.res, rv_simp]
theorem rl1030_spec (hpc : s.pc = pcOf 1030) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 1158 ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1030 codeAt_1030 s hpc (by simp [eblk_1030.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1030.res, E.eval]
  · ex_regs eblk_1030.res
  · intro A _ _; simp [eblk_1030.res, rv_simp]
theorem rl1158_spec (hpc : s.pc = pcOf 1158) (i n4 : Nat) (hi : i < 2 ^ 63) (hn : n4 < 2 ^ 63)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 i) (h27 : s.getReg .x27 = BitVec.ofNat 64 n4) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if i < n4 then pcOf 1160 else pcOf 1031) ∧
      t.getReg .x21 = BitVec.ofNat 64 3 ∧ RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1158 codeAt_1158 s hpc (by simp [eblk_1158.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1158.res, E.eval, CmpOp.eval, h19, h27]
    rw [ex_slt i n4 hi hn]
    by_cases hi' : i < n4 <;> simp [hi']
  · simp [eblk_1158.res, rv_simp]
  · ex_regs eblk_1158.res
  · intro A _ _; simp [eblk_1158.res, rv_simp]
theorem rl1160_spec (hpc : s.pc = pcOf 1160) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x21 = BitVec.ofNat 64 4 ∧
      RegsExcept s t [.x21] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1160 codeAt_1160 s hpc (by simp [eblk_1160.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1160.res, E.eval]
  · simp [eblk_1160.res, rv_simp]
  · ex_regs eblk_1160.res
  · intro A _ _; simp [eblk_1160.res, rv_simp]
theorem rl1031_spec (hpc : s.pc = pcOf 1031) (st e : Nat) (hs : st < 2 ^ 63) (he : e < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 st) (h21 : s.getReg .x21 = BitVec.ofNat 64 e) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if e ≤ st then pcOf 1049 else pcOf 1032) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1031 codeAt_1031 s hpc (by simp [eblk_1031.res, rv_simp]), ?_, ?_, ?_⟩
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
    ∃ t, Steps image s (Keygen.headerK lay) (Keygen.headerK lay) t ∧ t.pc = pcOf 1046 ∧
      t.getReg .x10 = BitVec.ofNat 64 CHAIN ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (CHAIN + 48) ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 16)) = (T3.chainHeader lay tree leaf i st).extractLsb' 0 64 ∧
      t.getMem (BitVec.ofNat 64 (CHAIN + 24)) = (T3.chainHeader lay tree leaf i st).extractLsb' 64 64 ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x28, .x30] ∧
      Frame s t (fun A => A = CHAIN + 16 ∨ A = CHAIN + 24) := by
  have run : ∃ t, Steps image s (Keygen.headerK lay) (Keygen.headerK lay) t ∧
      t.pc = pcOf 1046 ∧ Keygen.PackedBlocks.HeaderPost s t (T3.height lay) := by
    fin_cases lay
    · exact Keygen.PackedBlocks.expand_header_0 s hpc h8
    · exact Keygen.PackedBlocks.expand_header_1 s hpc h8
    · exact Keygen.PackedBlocks.expand_header_2 s hpc h8
    · exact Keygen.PackedBlocks.expand_header_3 s hpc h8
  obtain ⟨t, steps, pc, post⟩ := run
  refine ⟨t, steps, pc, post.arg0, post.arg1, post.arg2,
    post.low.trans (Keygen.PackedBlocks.packedAt_source s lay tree leaf i st hr hf hi hs h8 h9 h18 h19 h20),
    ?_, post.regs, post.frame⟩
  exact (post.high.trans (Keygen.PackedBlocks.routedAt_high_zero s lay tree leaf hr h9 h18)).trans
    (Keygen.PackedBlocks.source_high_actual lay tree leaf i st hr hf hi hs).symm
theorem fetch_1046 (hpc : s.pc = pcOf 1046) : fetch image s = some (.base .ECALL) :=
  (codeAt_1046.fetch s hpc).trans rfl
theorem rl1047_spec (hpc : s.pc = pcOf 1047) (st : Nat) (h20 : s.getReg .x20 = BitVec.ofNat 64 st) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = pcOf 1031 ∧ t.getReg .x20 = BitVec.ofNat 64 (st + 1) ∧
      RegsExcept s t [.x20] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1047 codeAt_1047 s hpc (by simp [eblk_1047.res, rv_simp]), ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1047.res, E.eval]
  · simp only [Result.toState_getReg, eblk_1047.res, rv_simp, h20, ofNat_add_ofNat]
  · ex_regs eblk_1047.res
  · intro A _ _; simp [eblk_1047.res, rv_simp]
theorem rl1049_spec (hpc : s.pc = pcOf 1049) (lay : T3.Layer) (i : Nat) (hi : i < 2 ^ 59)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay.val) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s (slK lay i) (slK lay i) t ∧ t.pc = pcOf 1052 ∧
      t.getReg .x28 = BitVec.ofNat 64 (slotOff lay i) ∧ RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  have hl := lay.isLt
  obtain ⟨t1, s1, p1, r1, f1⟩ : ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf 42758 ∧ RegsExcept s t [] ∧
      Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eblk_1049 codeAt_1049 s hpc (by simp [eblk_1049.res, rv_simp]), ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eblk_1049.res, E.eval]
    · intro r hr; cases r <;> rfl
    · intro A hA hn; rfl
  have g8 : t1.getReg .x8 = BitVec.ofNat 64 lay.val := by rw [r1.get (by decide), h8]
  have g19 : t1.getReg .x19 = BitVec.ofNat 64 i := by rw [r1.get (by decide), h19]
  obtain ⟨t2, s2, p2, x28, r2, f2⟩ : ∃ t, Steps image t1 2 2 t ∧
      t.pc = (if lay = 0 then pcOf 42763 else pcOf 42760) ∧ t.getReg .x28 = BitVec.ofNat 64 (16 * i) ∧
      RegsExcept t1 t [.x28] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_slA e_slA_at t1 p1 (by simp [eb_slA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
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
    obtain ⟨t3, s3, p3, y28, r3, f3⟩ : ∃ t, Steps image t2 2 2 t ∧ t.pc = pcOf 1052 ∧
        t.getReg .x28 = BitVec.ofNat 64 (16 * i + 32) ∧ RegsExcept t2 t [.x28] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slT e_slT_at t2 p2 (by simp [eb_slT.res, rv_simp]), ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_slT.res, E.eval]
      · simp only [Result.toState_getReg, eb_slT.res, rv_simp, x28, ofNat_add_ofNat]
      · ex_regs eb_slT.res
      · intro A _ _; simp [eb_slT.res, rv_simp]
    refine ⟨t3, ((s1.trans s2).trans s3).of_eq (by simp [slK, h0]) (by simp [slK, h0]), p3,
      by rw [y28, slotOff, if_pos h0], ((r1.trans r2).trans r3).mono (by decide),
      ((f1.trans f2).trans f3).mono (fun A _ h => by simp_all)⟩
  · rw [if_neg h0] at p2
    have g19' : t2.getReg .x19 = BitVec.ofNat 64 i := by rw [r2.get (by decide), g19]
    obtain ⟨t3, s3, p3, r3, f3⟩ : ∃ t, Steps image t2 1 1 t ∧
        t.pc = (if i = 0 then pcOf 42764 else pcOf 42761) ∧ RegsExcept t2 t [] ∧ Frame t2 t (fun _ => False) := by
      refine ⟨_, symRun_sound eb_slB e_slB_at t2 p2 (by simp [eb_slB.res, rv_simp]), ?_, ?_, ?_⟩
      · simp only [Result.toState_pc, eb_slB.res, E.eval, CmpOp.eval, g19']
        rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq i 0 (by omega) (by norm_num)]
        by_cases hc : i = 0 <;> simp [hc]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    by_cases hi0 : i = 0
    · rw [if_pos hi0] at p3
      obtain ⟨t4, s4, p4, r4, f4⟩ : ∃ t, Steps image t3 1 1 t ∧ t.pc = pcOf 1052 ∧ RegsExcept t3 t [] ∧
          Frame t3 t (fun _ => False) := by
        refine ⟨_, symRun_sound eb_slZ e_slZ_at t3 p3 (by simp [eb_slZ.res, rv_simp]), ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_slZ.res, E.eval]
        · intro r hr; cases r <;> rfl
        · intro A hA hn; rfl
      refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, h0, hi0]) (by simp [slK, h0, hi0]), p4,
        by rw [r4.get (by decide), r3.get (by decide), x28, slotOff, if_neg h0, if_pos hi0, hi0],
        (((r1.trans r2).trans r3).trans r4).mono (by decide),
        (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
    · rw [if_neg hi0] at p3
      have y28 : t3.getReg .x28 = BitVec.ofNat 64 (16 * i) := by rw [r3.get (by decide), x28]
      obtain ⟨t4, s4, p4, z28, r4, f4⟩ : ∃ t, Steps image t3 2 2 t ∧ t.pc = pcOf 1052 ∧
          t.getReg .x28 = BitVec.ofNat 64 (16 * i + 16) ∧ RegsExcept t3 t [.x28] ∧ Frame t3 t (fun _ => False) := by
        refine ⟨_, symRun_sound eb_slN e_slN_at t3 p3 (by simp [eb_slN.res, rv_simp]), ?_, ?_, ?_, ?_⟩
        · simp [Result.toState_pc, eb_slN.res, E.eval]
        · simp only [Result.toState_getReg, eb_slN.res, rv_simp, y28, ofNat_add_ofNat]
        · ex_regs eb_slN.res
        · intro A _ _; simp [eb_slN.res, rv_simp]
      refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by simp [slK, h0, hi0]) (by simp [slK, h0, hi0]), p4,
        by rw [z28, slotOff, if_neg h0, if_neg hi0], (((r1.trans r2).trans r3).trans r4).mono (by decide),
        (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
theorem rl1052_spec (hpc : s.pc = pcOf 1052) (i x : Nat) (hx8 : x % 8 = 0) (hx : LEAFPK + x + 16 ≤ 2 ^ 24)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 x) (h19 : s.getReg .x19 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 11 11 t ∧ t.pc = pcOf 1010 ∧ t.getReg .x19 = BitVec.ofNat 64 (i + 1) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x)) = s.getMem (BitVec.ofNat 64 (CHAIN + 48)) ∧
      t.getMem (BitVec.ofNat 64 (LEAFPK + x + 8)) = s.getMem (BitVec.ofNat 64 (CHAIN + 56)) ∧
      RegsExcept s t [.x6, .x7, .x19, .x28, .x29] ∧
      Frame s t (fun A => A = LEAFPK + x ∨ A = LEAFPK + x + 8) := by
  refine ⟨_, symRun_sound eblk_1052 codeAt_1052 s hpc (by
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
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf 1072 ∧ t.getReg .x10 = BitVec.ofNat 64 LEAFPK ∧
      t.getReg .x11 = BitVec.ofNat 64 ((16 * (n + 1) + 63) / 64 * 64) ∧ t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x10, .x11, .x12] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1063 codeAt_1063 s hpc (by simp [eblk_1063.res, rv_simp]),
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
theorem fetch_1072 (hpc : s.pc = pcOf 1072) : fetch image s = some (.base .ECALL) :=
  (codeAt_1072.fetch s hpc).trans rfl
theorem rl1073_spec (hpc : s.pc = pcOf 1073) (P n : Nat) (hP : P + 16 * n < 2 ^ 64)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 P) (h26 : s.getReg .x26 = BitVec.ofNat 64 n) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x22 = BitVec.ofNat 64 (P + 16 * n) ∧ RegsExcept s t [.x20, .x22, .x28] ∧
      Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1073 codeAt_1073 s hpc (by simp [eblk_1073.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
  · simp [Result.toState_pc, eblk_1073.res, E.eval]
  · simp [eblk_1073.res, rv_simp]
  · simp only [Result.toState_getReg, eblk_1073.res, rv_simp, h16, h26]
    t3n []; congr 1; ring
  · ex_regs eblk_1073.res
  · intro A _ _; simp [eblk_1073.res, rv_simp]
theorem rl1076_spec (hpc : s.pc = pcOf 1076) (j hh : Nat) (hj : j < 2 ^ 63) (hh' : hh < 2 ^ 63)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = (if hh ≤ j then pcOf 1143 else pcOf 1077) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1076 codeAt_1076 s hpc (by simp [eblk_1076.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1076.res, E.eval, CmpOp.eval, h20, h15]
    rw [ex_slt j hh hj hh']
    by_cases hc : hh ≤ j
    · simp [hc, show ¬ j < hh by omega]
    · simp [hc, show j < hh by omega]
  · ex_regs eblk_1076.res
  · intro A _ _; simp [eblk_1076.res, rv_simp]
theorem rl1077_spec (hpc : s.pc = pcOf 1077) (leaf j : Nat) (hl : leaf < 2 ^ 64) (hj : j < 64)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = (if leaf / 2 ^ j % 2 = 0 then pcOf 1099 else pcOf 1080) ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1077 codeAt_1077 s hpc (by simp [eblk_1077.res, rv_simp]), ?_, ?_, ?_⟩
  · simp only [Result.toState_pc, eblk_1077.res, E.eval, CmpOp.eval, BinOp.eval, h18, h20]
    rw [toNat_ofNat_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hj, ofNat_shr _ _ hl, ofNat_and1,
      show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq _ 0 (by omega) (by norm_num)]
    by_cases hc : leaf / 2 ^ j % 2 = 0
    · simp [hc]
    · simp [hc]
  · ex_regs eblk_1077.res
  · intro A _ _; simp [eblk_1077.res, rv_simp]
theorem ex_ne (x y : Nat) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) (h : x ≠ y) : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y :=
  fun he => h ((ofNat_inj hx hy).mp he)
theorem ex_valid (x : Nat) (h1 : x % 8 = 0) (h2 : x + 8 ≤ 2 ^ 24) : accessValid (BitVec.ofNat 64 x) 8 = true := by
  rw [accessValid_iff, toNat_ofNat_lt (by omega)]; simp only [MEMORY_BYTES]; omega
theorem rl1080_spec (hpc : s.pc = pcOf 1080) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps image s 19 19 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 M) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M ∨ A = M + 8 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1080 codeAt_1080 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
theorem rl1099_spec (hpc : s.pc = pcOf 1099) (P M : Nat) (hP8 : P % 8 = 0) (hP : 0x7000 ≤ P) (hP' : P + 16 ≤ 0x7000 + 5616)
    (hM8 : M % 8 = 0) (hM : 0x800 ≤ M) (hM' : M + 64 ≤ 0x7000)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t, Steps image s 18 18 t ∧ t.pc = pcOf 1117 ∧
      t.getMem (BitVec.ofNat 64 (M + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (M + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      t.getMem (BitVec.ofNat 64 NODE) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 48)) = s.getMem (BitVec.ofNat 64 P) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 56)) = s.getMem (BitVec.ofNat 64 (P + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧
      Frame s t (fun A => A = M + 48 ∨ A = M + 56 ∨ A = NODE ∨ A = NODE + 8 ∨ A = NODE + 48 ∨ A = NODE + 56) := by
  refine ⟨_, symRun_sound eblk_1099 codeAt_1099 s hpc ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eblk_1099.res, Result.obligs, Oblig.all, Oblig.holds, Addr.eval, E.eval, BinOp.eval, RegFile.get,
      h22, h24, ofNat_add_ofNat, BitVec.ofNat_eq_ofNat, add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | exact ex_valid _ (by omega) (by omega)
        | exact ex_ne _ _ (by omega) (by omega) (by omega)
  · simp [Result.toState_pc, eblk_1099.res, E.eval]
  iterate 6
    · simp only [Result.toState_getMem, eblk_1099.res, NODE, NOUT]
      t3n [h22, h24]
      all_goals ((try split_ifs) <;> first | (exfalso; omega) | (congr 2; ring) | rfl)
  · ex_regs eblk_1099.res
  · intro A hA hn
    simp only [NODE] at hn
    simp only [Result.toState_getMem, eblk_1099.res]
    t3n [h24]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
theorem rl1119_spec (hpc : s.pc = pcOf 1119) (lay tree leaf hh j : Nat) (hlay : lay < 4) (htree : tree < 2 ^ 32)
    (hl : leaf < 2 ^ 32) (hj : j < hh) (hh' : hh ≤ 12)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 lay) (h9 : s.getReg .x9 = BitVec.ofNat 64 tree)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) (h15 : s.getReg .x15 = BitVec.ofNat 64 hh)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h28 : s.getReg .x28 = BitVec.ofNat 64 (hh - j - 1)) :
    ∃ t, Steps image s (hdrK lay) (hdrK lay) t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) =
        BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept s t [.x6, .x7, .x10, .x11, .x12, .x13, .x28, .x30] ∧
      Frame s t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
  obtain ⟨t1, s1, p1, x13, r1, f1⟩ : ∃ t, Steps image s 6 6 t ∧ t.pc = pcOf 42765 ∧
      t.getReg .x13 = BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) ∧
      RegsExcept s t [.x13, .x28] ∧ Frame s t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrA e_hdrA_at s hpc (by simp [eb_hdrA.res, rv_simp]), ?_, ?_, ?_, ?_⟩
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
  obtain ⟨t2, s2, p2, x7, x6, r2, f2⟩ : ∃ t, Steps image t1 3 3 t ∧
      t.pc = (if lay = 0 then pcOf 42776 else pcOf 42768) ∧
      t.getReg .x7 = BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) ∧
      t.getReg .x6 = BitVec.ofNat 64 64 ∧ RegsExcept t1 t [.x6, .x7] ∧ Frame t1 t (fun _ => False) := by
    refine ⟨_, symRun_sound eb_hdrB e_hdrB_at t1 p1 (by simp [eb_hdrB.res, rv_simp]), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Result.toState_pc, eb_hdrB.res, E.eval, CmpOp.eval, g8]
      rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ex_beq lay 0 (by omega) (by norm_num)]
      by_cases h0 : lay = 0 <;> simp [h0]
    · simp only [Result.toState_getReg, eb_hdrB.res, rv_simp, x13]
    · simp [eb_hdrB.res, rv_simp]
    · ex_regs eb_hdrB.res
    · intro A _ _; simp [eb_hdrB.res, rv_simp]
  obtain ⟨t3, s3, p3, y6, r3, f3⟩ : ∃ t, Steps image t2 (if lay = 0 then 1 else 9) (if lay = 0 then 1 else 9) t ∧
      t.pc = pcOf 1129 ∧ t.getReg .x6 = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
      RegsExcept t2 t [.x6, .x30] ∧ Frame t2 t (fun _ => False) := by
    by_cases h0 : lay = 0
    · rw [if_pos h0] at p2
      refine ⟨_, (symRun_sound eb_hdrD e_hdrD_at t2 p2 (by simp [eb_hdrD.res, rv_simp])).of_eq (by simp [h0, eb_hdrD.res])
        (by simp [h0, eb_hdrD.res]), ?_, ?_, ?_, ?_⟩
      · simp [Result.toState_pc, eb_hdrD.res, E.eval]
      · simp only [Result.toState_getReg, eb_hdrD.res, rv_simp, x6, Keygen.nodeLo, if_pos h0]
      · intro r hr; cases r <;> rfl
      · intro A hA hn; rfl
    · rw [if_neg h0] at p2
      have g8' : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [r2.get (by decide), g8]
      have g9' : t2.getReg .x9 = BitVec.ofNat 64 tree := by rw [r2.get (by decide), g9]
      refine ⟨_, (symRun_sound eb_hdrC e_hdrC_at t2 p2 (by simp [eb_hdrC.res, rv_simp])).of_eq (by simp [h0, eb_hdrC.res])
        (by simp [h0, eb_hdrC.res]), ?_, ?_, ?_, ?_⟩
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
      · ex_regs eb_hdrC.res
      · intro A _ _; simp [eb_hdrC.res, rv_simp]
  have y7 : t3.getReg .x7 = BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) := by
    rw [r3.get (by decide), x7]
  obtain ⟨t4, s4, p4, m16, m24, x10, x11, x12, r4, f4⟩ : ∃ t, Steps image t3 9 9 t ∧ t.pc = pcOf 1138 ∧
      t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 (Keygen.nodeLo lay tree) ∧
      t.getMem (BitVec.ofNat 64 (NODE + 24)) = BitVec.ofNat 64 (2 ^ (hh - j - 1) + leaf / 2 ^ (j + 1)) ∧
      t.getReg .x10 = BitVec.ofNat 64 NODE ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 NOUT ∧
      RegsExcept t3 t [.x10, .x11, .x12, .x28] ∧ Frame t3 t (fun A => A = NODE + 16 ∨ A = NODE + 24) := by
    refine ⟨_, symRun_sound eb_hdrE e_hdrE_at t3 p3 (by simp [eb_hdrE.res, rv_simp, accessValid_iff, MEMORY_BYTES]),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Result.toState_pc, eb_hdrE.res, E.eval]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y6]
    · simp only [Result.toState_getMem, eb_hdrE.res, NODE]
      t3n [y7]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · simp [eb_hdrE.res, rv_simp]
    · ex_regs eb_hdrE.res
    · intro A hA hn
      simp only [NODE] at hn
      simp only [Result.toState_getMem, eb_hdrE.res]
      t3n []
      rw [if_neg (by omega), if_neg (by omega)]
  refine ⟨t4, (((s1.trans s2).trans s3).trans s4).of_eq (by unfold hdrK; split_ifs <;> simp_all)
    (by unfold hdrK; split_ifs <;> simp_all), p4, m16, m24, x10, x11, x12,
    (((r1.trans r2).trans r3).trans r4).mono (by decide),
    (((f1.trans f2).trans f3).trans f4).mono (fun A _ h => by simp_all)⟩
theorem fetch_1138 (hpc : s.pc = pcOf 1138) : fetch image s = some (.base .ECALL) :=
  (codeAt_1138.fetch s hpc).trans rfl
theorem rl1139_spec (hpc : s.pc = pcOf 1139) (P M j : Nat) (hM : 64 ≤ M) (hM' : M < 2 ^ 64)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = pcOf 1076 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x22, .x24] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound eblk_1139 codeAt_1139 s hpc (by simp [eblk_1139.res, rv_simp]),
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
    ∃ t, Steps image s 9 9 t ∧ t.pc = pcOf ret ∧
      t.getMem (BitVec.ofNat 64 ENC) = s.getMem (BitVec.ofNat 64 NOUT) ∧
      t.getMem (BitVec.ofNat 64 (ENC + 8)) = s.getMem (BitVec.ofNat 64 (NOUT + 8)) ∧
      RegsExcept s t [.x6, .x7, .x29, .x30] ∧ Frame s t (fun A => A = ENC ∨ A = ENC + 8) := by
  refine ⟨_, symRun_sound eblk_1143 codeAt_1143 s hpc (by simp [eblk_1143.res, rv_simp]),
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
end blocks
end SigGolfCandidate.T3M.Expand
end
