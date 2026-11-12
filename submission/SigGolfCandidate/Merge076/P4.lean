import SigGolfCandidate.ExpandLabel
import SigGolfCandidate.Merge011
import SigGolfCandidate.Merge045
import SigGolfCandidate.Merge051
import SigGolfCandidate.Merge052
import SigGolfCandidate.Merge058
import SigGolfCandidate.Merge059
import SigGolfCandidate.Merge060
import SigGolfCandidate.Merge070
import SigGolfCandidate.Merge075
import SigGolfCandidate.Merge076.P1

set_option debug.skipKernelTC false
set_option linter.all false

-- ==== merged from T3M_Expand_LayerBlocks ====
section

section
namespace SigGolfCandidate.T3M.Expand.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
abbrev NODE : Nat := 0x20200
end SigGolfCandidate.T3M.Expand.BCBlocks
end
section
namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
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
/-- L-hyper A: the lower node base jumps (word 2) to the node marker trampoline `e_ndT` (245346), which returns to
43467 (where `or t1,t1,t5` ORs the marker again). -/
def e_hdrC : List (BitVec 32) := [0x1049313,0x20136313,0x541c506f,0x13,0x13,0x13,0x13,0x13]
def e_ndT : List (BitVec 32) := [0x141f13,0x1e40433,0x840433,0xc43f13,0x1f4f13,0x1f0f13,0x16f1f13,0x8f1f33,0x1e36333,0x840413,0x345413,0xd793a06f]
sym_block eb_hdrC0 := symRun { noAlias := true } e_hdrC (pcOf 42768) 30
sym_block eb_hdrC := symRunAux { noAlias := true } e_ndT (pcOf 245346) 30 eb_hdrC0.res.st
def e_hdrD : List (BitVec 32) := [ExpandLabel.jump]
sym_block eb_hdrD := symRun { noAlias := true } e_hdrD (pcOf 42776) 30
def e_hdrE : List (BitVec 32) := [134711,537792019,7223331,8272931,132407,537199891,67110291,132663,604374547]
sym_block eb_hdrE := symRun { noAlias := true } e_hdrE (pcOf 1129) 30
/-- L-hyper A: the leaf prologue jumps (word 4) to the marker trampoline `e_hpT` (245335), back at word 9. -/
def e_hpA : List (BitVec 32) := [0xf49333,0x1230333,0x1031313,0x13,0x579c506f,0x13,0x13,0x13,0x13,0x20e37,0x600e0e13,0x6e3823,0xe3c23,0x41663]
def e_hpT : List (BitVec 32) := [0x141f13,0x1e40433,0x840433,0x803f33,0x1f0f13,0x1cf1f13,0x8f1f33,0x1e36333,0x640413,0x345413,0xa743a06f]
sym_block eb_hpA0 := symRun { noAlias := true } e_hpA (pcOf 42741) 30
sym_block eb_hpT := symRunAux { noAlias := true } e_hpT (pcOf 245335) 30 eb_hpA0.res.st
sym_block eb_hpA := symRunAux { noAlias := true } (e_hpA.drop 9) (pcOf 42750) 30 eb_hpT.res.st
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
/-- C2 (FULL) + C4: offset of the current value (a left child) in the node output: every layer reads the high half. -/
def hiOff (_lay : Nat) : Nat := 16
def hdrK (lay : Nat) : Nat := if lay = 0 then 31 else 38
section blocks
variable (s : MachineState)
theorem eb_ct3_regs (t : MachineState) : RegsExcept t (eb_ct3.res.toState t) [.x6, .x7, .x20, .x28] := by
  intro r hr; simp at hr; cases r <;> simp_all [eb_ct3.res, rv_simp] <;> rfl
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
end blocks
end SigGolfCandidate.T3M.Expand
end

namespace SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand.BCBlocks
variable {im : Image}          
end SigGolfCandidate.T3M.Expand.SharedRecover.BCBlocks

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (DIGITS NODE NOUT ENC)
/-! img-v6 top-node nonce routine (words 43195 .. 43249, hooked at 1139 `jal 43195`; topfold-v6, NOTES V49). -/
def seg_n1139 : List (BitVec 32) := [0x1202906f]
/-- U16b: word 1138 is `jal 54800` (the grind stub); the stub words 54800..54885. -/
def seg_g1138 : List (BitVec 32) := [0x6783406f]
def cStub : List (BitVec 32) := [0x3e703423,0x3fc03823,0x3fd03c23,0x41e03023,0x41f03423,0x73,0x1053f83,0x8fd393,0xff3f393,0x700e13,0x11c39263,0x1cfd393,0x13,0xe038c63,0xffff393,0xf8038393,0x138ba06f,0x13,0x5e1e13,0x700f37,0x1cf0f33,0x2000e93,0xe1463,0x4000e93,0x1d3e463,0x7f3c23,0x2880506f,0xdc3f063,0x100e93,0x800e13,0x3c3f063,0x200e93,0x400e13,0x1c3fa63,0x1cfde13,0xfffe0e13,0xe1463,0x300e93,0x13fe13,0x1e4e13,0x4e1e13,0xce0f33,0xff0f13,0x8000f93,0x1df9fb3,0x800e13,0x41de0eb3,0xf4e03,0x1de5e33,0xe0e63,0x2053383,0x138393,0x1f3f863,0x2753023,0x73,0xfe1ff06f,0x1053f83,0xb4ba06f,0x13,0x5e1e13,0x700f37,0x1cf0f33,0x2480506f,0xf8038393,0xe93,0x400e13,0x1c3ea63,0x800e93,0x800e13,0x1c3e463,0x1000e93,0x1df0f33,0x2053383,0x7f3023,0x2053023,0x3e803383,0x3e003423,0x3f003e03,0x3e003823,0x3f803e83,0x3e003c23,0x40003f03,0x40003023,0x40803f83,0x40003423,0x839cb06f]
/-- L-hyper A: the layer decode trampolines (`t3 = [w ≥ 2^35] + [w ≥ 2^41] + [w ≥ 2^47]`, `t5` scratch). -/
def eDecT1 : List (BitVec 32) := [0x23fde13,0x1c03e33,0x29fdf13,0x1e03f33,0x1ee0e33,0x2ffdf13,0x1ee0e33,0xeb54506f]
def eDecT2 : List (BitVec 32) := [0x23fde13,0x1c03e33,0x29fdf13,0x1e03f33,0x1ee0e33,0x2ffdf13,0x1ee0e33,0xf394506f]
/-- E11: the grind tiers (60108..60127) and the post-grind nonce slot (60128..60141). -/
def cE11s : List (BitVec 32) := (Images.expandE11Code.drop 108).take 34
/-- N7g b rule (60968..60975, entered by `60115: jal 60968`): heaps 8..15 get `t4 = 2` on every lower layer. -/
def cBR : List (BitVec 32) := (Images.expandR6Code.drop 49).take 8
def seg_1140 : List (BitVec 32) := [4228647955,1706515,4020236399]
def nonce_A : List (BitVec 32) := [0xc00e13,0xdc79863]
def nonce_B : List (BitVec 32) := [0xb00e13,0xdca7463]
/-- T51: 43199 `addi a3,s4,1` (`h`), 43200 `j 54553` (ZB; #938 `mv a4,a3`, then 43201..43214 computed `b = h`). -/
def nonce_C : List (BitVec 32) := [0x1a0693,0x1640b06f]
/-! T51 ZB (54553..54568): `a4 = b_h = topZeroBits h` (0 for `h < 3`, 1 for `h = 3`, else `h - 3`) and the zero-test
mask `t6` (0 for `b_h = 0`, the top `b_h` bits, bits 40..47 for `h = 11`), then `j 43215`. -/
def nonce_Z0 : List (BitVec 32) := [0x00000713,0x00000f93,0x00300e13,0x03c6c863]
def nonce_Z1 : List (BitVec 32) := [0xffd68713,0x2d80006f]
def nonce_Z2 : List (BitVec 32) := [0x00100713,0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z3 : List (BitVec 32) := [0x04000e13,0x40ee0e33,0xfff00f93,0x01cf9fb3,0x00b00e13,0x01c69663]
def nonce_Z4 : List (BitVec 32) := [0x1ff00f93,0x2c80006f,0xe9df406f]
def nonce_Alloc0 : List (BitVec 32) := [0x71663,0x100713,0xd29ff06f,0x170713,0xd21ff06f]
def nonce_Alloc1 : List (BitVec 32) := [0x900713,0x23f9f93,0xd35ff06f]
def nonce_ZA0 : List (BitVec 32) := nonce_Alloc0.take 1
def nonce_ZA1 : List (BitVec 32) := (nonce_Alloc0.drop 1).take 2
def nonce_ZA2 : List (BitVec 32) := nonce_Alloc0.drop 3
def nonce_ZA3 : List (BitVec 32) := nonce_Alloc1
def nonce_Z5 : List (BitVec 32) := [0xe9df406f]
def nonce_F : List (BitVec 32) := [0x7ff00f93,0x22f9f93]
def nonce_G : List (BitVec 32) := [0x6800893,0xe898b3,0xd95eb3,0x1efe93,0x100f13,0x41df0eb3,0x4e9e93,0x20f37,0x240f0f13,0x1ee8eb3]
def nonce_L : List (BitVec 32) := [0x8ebf03,0x1ff7f33,0x20f0a63]
def nonce_H : List (BitVec 32) := [0x20e37,0x220e3f03,0x1f0f13,0x31f7263]
def nonce_I : List (BitVec 32) := [0x23ee3023,0x20537,0x20050513,0x4000593,0x20637,0x24060613]
def nonce_E43238 : List (BitVec 32) := [0x73]
def nonce_J : List (BitVec 32) := [0xfc9ff06f]
def nonce_K : List (BitVec 32) := [0x20e37,0x220e3f03,0x220e3023,0x66e37,0x752e3c23,0x3a1e93,0x1de0e33,0x71ee3023]
def nonce_S : List (BitVec 32) := [0x10b0b13,0xe0dd606f]
class Code (im : Image) : Prop where
  e_hdrA_at : CodeAt im (pcOf 1119) e_hdrA
  e_hdrB_at : CodeAt im (pcOf 42765) e_hdrB
  e_hdrC_at : CodeAt im (pcOf 42768) e_hdrC
  e_ndT_at : CodeAt im (pcOf 245346) e_ndT
  e_hdrD_at : CodeAt im (pcOf 42776) e_hdrD
  e_hdrWindow_at : CodeAt im (pcOf 1125) ExpandLabel.window
  e_hdrE_at : CodeAt im (pcOf 1129) e_hdrE
  e_hpA_at : CodeAt im (pcOf 42741) e_hpA
  e_hpT_at : CodeAt im (pcOf 245335) e_hpT
  e_hpA2_at : CodeAt im (pcOf 42750) (e_hpA.drop 9)
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
  codeAt_1138 : CodeAt im (pcOf 1138) seg_g1138
  codeAt_stub : CodeAt im (pcOf 54800) cStub
  codeAt_dec1 : CodeAt im (pcOf 245358) eDecT1
  codeAt_dec2 : CodeAt im (pcOf 245366) eDecT2
  codeAt_e11s : CodeAt im (pcOf 60108) cE11s
  codeAt_brule : CodeAt im (pcOf 60968) cBR
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
  codeAt_nZA0 : CodeAt im (pcOf 54740) nonce_ZA0
  codeAt_nZA1 : CodeAt im (pcOf 54741) nonce_ZA1
  codeAt_nZA2 : CodeAt im (pcOf 54743) nonce_ZA2
  codeAt_nZA3 : CodeAt im (pcOf 54745) nonce_ZA3
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
  e_hdrRemap_at : CodeAt im (pcOf 231593) ExpandLabel.remapCode
variable {im : Image} [Code im]
variable                    [PackedBlocks.Code im]
variable (s : MachineState)
theorem pe_ne {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = decide (x ≠ y) := by
  by_cases hxy : x = y
  · subst hxy; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun he => hxy ((ofNat_inj hx hy).mp he)
    simp [hxy, this]
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Expand
variable {im : Image} [Code im] (s : MachineState)
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace Grind
open SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest nonceBytes pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.WCT9 (lowerZeroBits lowerNonceCap lowerZeroOk lowerNodeInputN lowerNodeHashN lowerNonceSearch
  lowerNodeAt)
/-- Stub slice `[a, b)` (word indices). -/
def sl (a b : Nat) : List (BitVec 32) := (cStub.drop (a - 54800)).take (b - a)
def cfgS : Config := { noAlias := true }
/-- Initial symbolic state of the loop check with `t5 = a2 + K` (K = 15 or 31: the used half's top byte). -/
def σK (K : Nat) : SymState := ⟨RegFile.init.set .x30 (.bin .add (.reg .x12) (.c (BitVec.ofNat 64 K))), [], []⟩

sym_block gHd := symRun cfgS (sl 54800 54806) (pcOf 54800) 20
sym_block gB1 := symRun cfgS (sl 54806 54811) (pcOf 54806) 20
sym_block gB2 := symRun cfgS (sl 54811 54814) (pcOf 54811) 20
sym_block gB3 := symRun cfgS (sl 54814 54823) (pcOf 54814) 20
sym_block gB3T := symRunAux cfgS eDecT1 (pcOf 245358) 20 gB3.res.st
sym_block gB3R := symRunAux cfgS (sl 54818 54823) (pcOf 54818) 20 gB3T.res.st
sym_block gB3a := symRun cfgS (sl 54823 54825) (pcOf 54823) 20
sym_block gB3b := symRun cfgS (sl 54824 54825) (pcOf 54824) 20
sym_block gB4a := symRun cfgS (sl 54825 54827) (pcOf 54825) 20
sym_block gB4b := symRun cfgS (sl 54826 54827) (pcOf 54826) 20
sym_block gB8b := symRun cfgS (sl 54838 54847) (pcOf 54838) 20
sym_block gLc15 := symRunAux cfgS (sl 54847 54850) (pcOf 54847) 20 (σK 15)
sym_block gLc31 := symRunAux cfgS (sl 54847 54850) (pcOf 54847) 20 (σK 31)
sym_block gL2 := symRun cfgS (sl 54850 54853) (pcOf 54850) 20
sym_block gL3 := symRun cfgS (sl 54853 54855) (pcOf 54853) 20
sym_block gL4 := symRun cfgS (sl 54855 54856) (pcOf 54855) 20
sym_block gF1 := symRun cfgS (sl 54856 54863) (pcOf 54856) 20
sym_block gF1T := symRunAux cfgS eDecT2 (pcOf 245366) 20 gF1.res.st
sym_block gF1R := symRunAux cfgS (sl 54859 54863) (pcOf 54859) 20 gF1T.res.st
sym_block gF3b := symRun cfgS (sl 54872 54886) (pcOf 54872) 20
sym_block gDn := symRun cfgS (sl 54875 54886) (pcOf 54875) 20
/-- E11 slice `[a, b)` of the tier / post-grind code at 60108. -/
def slE (a b : Nat) : List (BitVec 32) := (cE11s.drop (a - 60108)).take (b - a)
sym_block tA := symRun cfgS (slE 60108 60112) (pcOf 60108) 20
sym_block tB := symRun cfgS (slE 60112 60115) (pcOf 60112) 20
/-- N7g b-rule slice `[a, b)` of the code at 60968. -/
def slB (a b : Nat) : List (BitVec 32) := (cBR.drop (a - 60968)).take (b - a)
sym_block tC0 := symRun cfgS (slE 60115 60116) (pcOf 60115) 20
sym_block tC1 := symRun cfgS (slB 60968 60971) (pcOf 60968) 20
sym_block tC2 := symRun cfgS (slB 60971 60974) (pcOf 60971) 20
sym_block tC3 := symRun cfgS (slB 60974 60976) (pcOf 60974) 20
sym_block tD := symRun cfgS (slE 60118 60121) (pcOf 60118) 20
sym_block tE := symRun cfgS (slE 60121 60125) (pcOf 60121) 20
sym_block tF := symRun cfgS (slE 60125 60127) (pcOf 60125) 20
sym_block tJ := symRun cfgS (slE 60126 60127) (pcOf 60126) 20
sym_block tK := symRun cfgS (slE 60127 60128) (pcOf 60127) 20
sym_block pA := symRun cfgS (slE 60128 60133) (pcOf 60128) 20
sym_block pB := symRun cfgS (slE 60133 60136) (pcOf 60133) 20
sym_block pC := symRun cfgS (slE 60136 60139) (pcOf 60136) 20
sym_block pD := symRun cfgS (slE 60139 60142) (pcOf 60139) 20
sym_block pE := symRun cfgS (slE 60140 60142) (pcOf 60140) 20
sym_block gJ := symRun cfgS seg_g1138 (pcOf 1138) 4

theorem code_sl {im : Image} (h : CodeAt im (pcOf 54800) cStub) (a b : Nat) (ha : 54800 ≤ a) (hb : b ≤ 54886)
    (hab : a ≤ b) : CodeAt im (pcOf a) (sl a b) := by
  have := codeAt_sub (a - 54800) h (seg := sl a b) (by simp [sl, show cStub.length = 86 from rfl]; omega)
    (by simp [sl])
  rwa [show 54800 + (a - 54800) = a by omega] at this
theorem code_slE {im : Image} (h : CodeAt im (pcOf 60108) cE11s) (a b : Nat) (ha : 60108 ≤ a) (hb : b ≤ 60142)
    (hab : a ≤ b) : CodeAt im (pcOf a) (slE a b) := by
  have := codeAt_sub (a - 60108) h (seg := slE a b) (by simp [slE, show cE11s.length = 34 from rfl]; omega)
    (by simp [slE])
  rwa [show 60108 + (a - 60108) = a by omega] at this
theorem code_slB {im : Image} (h : CodeAt im (pcOf 60968) cBR) (a b : Nat) (ha : 60968 ≤ a) (hb : b ≤ 60976)
    (hab : a ≤ b) : CodeAt im (pcOf a) (slB a b) := by
  have := codeAt_sub (a - 60968) h (seg := slB a b) (by simp [slB, show cBR.length = 8 from rfl]; omega)
    (by simp [slB])
  rwa [show 60968 + (a - 60968) = a by omega] at this

theorem σK_toState (K : Nat) (s : MachineState) (h30 : s.getReg .x30 = s.getReg .x12 + BitVec.ofNat 64 K) :
    (σK K).toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  cases r <;> first | rfl | (simp only [SymState.toState, σK, RegFile.set, RegFile.get, RegFile.init, E.eval]; exact h30.symm)

theorem nb_ult' (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

section blocks
variable {im : Image} [Code im] (s : MachineState)

end blocks

/-! U16b grind stub: tweak-word arithmetic. -/

theorem and255 (w : Word) : (w &&& 255#64).toNat = w.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
theorem ult_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a).ult (BitVec.ofNat 64 b) = decide (a < b) := nb_ult' a b ha hb

section cls
variable {im : Image} [Code im]

end cls

/-! U16b grind stub: loop setup and the zero test. -/

section setup
variable {im : Image} [Code im]

end setup

/-! U16b grind stub: node input, zero test, trial invariant. -/

section sim
variable {im : Image} {sk : BitVec 256}
end sim

theorem dig_half (t : MachineState) (a : BitVec 256) (B : Nat) (h12 : t.getReg .x12 = BitVec.ofNat 64 B)
    (hB : B + 32 < 2 ^ 64) (b : Bool) :
    DigAt (writeHash t a) (B + if b then 16 else 0) (ClaudeWCT.WCT9.halfOf b a) := by
  cases b
  · simpa using DigAt.writeHash_lo t a B h12 hB
  · simpa using DigAt.writeHash_hi t a B h12 hB

section found
variable {im : Image} [Code im]

end found

/-! U16b grind stub: the search loop and the whole stub (word 1138 -> 1139). -/

theorem zb_range (lay heap : Nat) (hg : lowerZeroBits lay heap ≠ 0) :
    1 ≤ lowerZeroBits lay heap ∧ lowerZeroBits lay heap ≤ 4 := by
  unfold ClaudeWCT.WCT9.lowerZeroBits at *; split_ifs at * <;> omega
section loop
variable {im : Image} [Code im] (sk : BitVec 256)

end loop

/-! U16b grind stub: the pass-through of a non-lower node (top tree). -/

section pass
variable {im : Image} [Code im] {sk : BitVec 256}

end pass

end Grind


end SigGolfCandidate.T3M.Expand.SharedRecover
end
-- ==== merged from T3M_Expand_Basic ====
section

namespace SigGolfCandidate.T3M.Expand
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
section tb
variable {image : Image} {sk : BitVec 256}
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
section chain
variable {sk : BitVec 256}
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
variable {im : Image} [Code im]                    [PackedBlocks.Code im] {sk : BitVec 256}
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
section blocks
variable (s : MachineState)
-- [h2 lane] removed c342_spec: a fact about the record's original expand word 0 / 342, which H2 replaces
end blocks
def lR2 (lay : Layer) : Nat := ![342, 318, 295, 272] lay
def lWC (lay : Layer) : Nat := ![0x3c88, 0x4908, 0x5548, 0x6188] lay
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
variable {im : Image}               
section
variable (s : MachineState)
end
end SigGolfCandidate.T3M.Expand.SharedRecover

namespace SigGolfCandidate.T3M.Expand.SharedRecover
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option Elab.async false
end SigGolfCandidate.T3M.Expand.SharedRecover

/-! ## T51 KCOPY (54522..54531, from 331 `jal ra, 54522`): copy the 1,896-byte shared kernel table window
`0xFF9E00 .. 0xFFA568` (237 doublewords; the 1,892-byte block + 4 bytes) to RAM `0xA0000`, then `j 457`. -/
namespace SigGolfCandidate.T3M.Expand.KCopy
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

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
end blocks
section sort
variable {image : Image} {b : Nat}
end sort
section loop
variable {image : Image} {b : Nat}
end loop
end SigGolfCandidate.T3M.Search
end
section
namespace SigGolfCandidate.T3M.Search
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
set_option linter.unusedSimpArgs false
theorem gate_jump_spec {image : Image} {b : Nat} (hK : KernAt image b) (hG : GateAt image b)
    (s : MachineState) (hpc : s.pc = pcOf (gatePc b + 5)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = pcOf (b + 3) ∧
      RegsExcept s t [] ∧ Frame s t (fun _ => False) := by
  refine ⟨_, symRun_sound (run_gateJump hK.2.1) (codeAt_gateJump hG) s hpc
    (by simp [blkGateJE.res, rv_simp]), ?_, ?_, ?_⟩
  · simp [E.eval]
  · intro r hr; cases r <;> simp [blkGateJE.res, rv_simp] <;> rfl
  · intro A _ _; simp [blkGateJE.res, rv_simp]
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
section blocks
variable {image : Image} {d b : Nat}
end blocks
theorem NAt.writeHash (t : MachineState) (a : BitVec 256) (h12 : t.getReg .x12 = BitVec.ofNat 64 NBUF) :
    NAt (writeHash t a) a := by
  intro j hj
  rw [getMem_writeHash t a NBUF _ h12 (by decide) (by simp only [NBUF]; omega)]
  interval_cases j <;> simp
section loop
variable {image : Image} {d b : Nat} {sk : BitVec 256}
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
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.ESearch
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
open SigGolfCandidate.T3M.Search (DIG NBUF FailedAt)
open SigGolfCandidate.T3M.Expand (IDXV)
open SphincsSecurity (bytesLE bytesLE_length)
open ClaudeWCT.W9.Machine.Sign (run memEval_cons_ofNat)
open ClaudeWCT.W9.Machine.Sign.SearchM (cst rfs mw ctrE grpE fieldE fieldLen idxE costByte costChk
  costChk_getD costByte_lt piece regs_rfs shl0_shr33 sll_eval srl_eval fieldE_eval psum psum_succ psum_le fieldN_lt
  psum_nine digestInput_length' pad64_digestInput' wordsOf_digestInput' blocks_digestInput' childN childN_lt childE_eval)
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
theorem expCostBytes_length : expCostBytes.length = 16384 := by decide +kernel
section pieces
variable {im : Image}
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
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
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
end ClaudeWCT.W9.Machine.Expand
end
section
namespace ClaudeWCT.W9.Machine.Expand.Driver
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M ClaudeWCT.W9.Machine.Expand
set_option maxRecDepth 16384
end ClaudeWCT.W9.Machine.Expand.Driver
end
section
namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput)
set_option linter.unusedSimpArgs false
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
/-- The 8 leaf digests (T8): `end0 | header | pad (honest 0) | end1..end5`. -/
def leafFields (k index j : Nat) (ends : List Digest) (i : Nat) : Digest :=
  if i = 0 then ends.getD 0 0 else if i = 1 then ClaudeWCT.WCT9.ftsLeafHeader index k j
  else if i = 2 then 0 else ends.getD (i - 2) 0
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
def cClr0 : List (BitVec 32) := [0x00006537,0x9e050513,0x000065b7,0x60058593]
end ClaudeWCT.W9.Machine.Expand.Layout
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_CompactCode ====
section

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib

namespace PairCopy
/-! Pairing stage 1: the lower-chain pair copy block at 48000 (outside the compact lookup scope). -/
end PairCopy
end ClaudeWCT.W9.Machine.Expand

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
/-- Nested FTS (r1-1): hold slot of coordinate `k` (top sibling, flag `1 - bit6`), written by the staging pass. -/
def holdAt (k : Nat) : Nat := 0x380000 + 32 * k
section code
variable {im : Image}                        
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact

namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.VLib
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
/-- Window `[compactChunkLo c, compactChunkLen c)` of image chunk `c` used by `compactScope` (chunk 169 only for the
stage-2 trampolines and C4 prefix; chunk 170 stops before the paired suffix jump at 43761). -/
def compactChunkLo (c : Nat) : Nat := if c=169 then 208 else 0
def compactChunkLen (c : Nat) : Nat := if c=172 then 12 else if c=170 then 241 else 256
end ClaudeWCT.W9.Machine.Expand
end
-- ==== merged from ClaudeWCT_W9_New_Machine_Expand_Compact2Lv ====
section

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
def cHolds : List (List (BitVec 32)) := [[3673655,17710979,933507,9322243,8361619,5218195,32933555,9015,201523987,6719155,4023824419,4024874019],[3673655,51265411,34487939,42876675,8361619,5218195,32933555,9015,3556967187,6719155,4057380899,4058430499],[3673655,84819843,68042371,76431107,8361619,5218195,32933555,9015,2617443091,6719155,4124487715,4125537315],[3673655,118374275,101596803,109985539,8361619,5218195,32933555,4919,1677918995,6719155,4158044195,4159093795],[3673655,151928707,135151235,143539971,8361619,5218195,32933555,4919,738394899,6719155,4225151011,4226200611],[3673655,185483139,168705667,177094403,8361619,5218195,32933555,4919,4093838099,6719155,4258707491,4259757091],[3673655,219037571,202260099,210648835,8361619,5218195,32933555,4919,3154314003,6719155,30847011,31896611],[3673655,252592003,235814531,244203267,8361619,5218195,32933555,4919,2214789907,6719155,30847011,31896611],[3673655,286146435,269368963,277757699,8361619,5218195,32933555,823,1275265811,6719155,30847011,31896611]]
def cPEnd : List (BitVec 32) := [990937199]
def cHold (c : Nat) : List (BitVec 32) := cHolds.getD c []
def cCh1 : List (BitVec 32) := [3224887,545588499,17847,3498411411,1591,361104915,533745903]
section code
variable {im : Image}                                                    
-- (include dropped in this part)
end code
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section


namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
section eval
variable {s : MachineState} {r : Nat} (h19 : s.getReg .x19 = BitVec.ofNat 64 r) (hr : r < 2 ^ 7)
include h19 hr
end eval
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end

section
namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
-- (open dropped: nothing it names is in this part)
set_option linter.unusedSimpArgs false
/-! C3 (FULL, E6): the root level of each lower layer runs in three pieces: `cLvA` (Z low word copy, then
`jal rtAt`), the trampoline `cRT` (Z high word copy, LE64(1) at window + 24, `jal` back) and `cLvB` (sibling copy). -/
section
variable {im : Image}                                                    
-- (include dropped in this part)
end
end ClaudeWCT.W9.Machine.Expand.Compact2
end
end
