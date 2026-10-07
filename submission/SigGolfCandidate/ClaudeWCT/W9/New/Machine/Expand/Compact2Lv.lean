import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCode
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Layout

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cSnap : List (BitVec 32) := [5431,0x80050513,3147191,361875,5687,0xaa960613,0xfb9ff0ef]
def cZero2 : List (BitVec 32) := [5559,0x80058593,5687,0xa7e60613,0xfc1ff0ef]
def cHdr : List (BitVec 32) := [3147063,328979,5559,0x80058593,1591,8783379,0xf89ff0ef]
def cReg8 : List (BitVec 32) := [3155255,0xc4050513,5559,0x84058593,1591,0x7060613,0xf6dff0ef]
def cReg7 : List (BitVec 32) := [3155255,0x8c050513,5559,0xbb058593,1591,0x7060613,0xf51ff0ef]
def cReg6 : List (BitVec 32) := [3151159,0x54050513,5559,0xf2058593,1591,0x7060613,0xf35ff0ef]
def cReg5 : List (BitVec 32) := [3151159,470091027,5559,688227731,1591,0x7060613,0xf19ff0ef]
def cReg4 : List (BitVec 32) := [3151159,0xe4050513,5559,0x60058593,1591,0x7060613,0xefdff0ef]
def cReg3 : List (BitVec 32) := [3151159,0xac050513,9655,0x97058593,1591,0x7060613,0xee1ff0ef]
def cReg2 : List (BitVec 32) := [3147063,0x74050513,9655,0xce058593,1591,0x7060613,0xec5ff0ef]
def cReg1 : List (BitVec 32) := [3147063,0x3c050513,9655,84247955,1591,0x7060613,0xea9ff0ef]
def cReg0 : List (BitVec 32) := [3147063,67437843,9655,0x3c058593,1591,0x7060613,0xe8dff0ef]
def cTop : List (BitVec 32) := [3155255,0xfc850513,9655,0x74058593,1591,554042899,0xe71ff0ef]
def cIdx : List (BitVec 32) := [0x6003b03,35347219,0xff9937,0x40090913]
def cCh1 : List (BitVec 32) := [3159351,545588499,17847,0x93058593,1591,361104915,0xe45ff0ef]
def cRow1 : List (BitVec 32) := [0xcb5993,0x7f9f993,3774995,19532339,537528851]
def cLv10 : List (BitVec 32) := [3159351,478479635,672515,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv11 : List (BitVec 32) := [3159351,411370771,1721091,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv12 : List (BitVec 32) := [3159351,344261907,2769667,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv13 : List (BitVec 32) := [3159351,277153043,3818243,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv14 : List (BitVec 32) := [3159351,0xc850513,4866819,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv15 : List (BitVec 32) := [3159351,0x8850513,5915395,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv16 : List (BitVec 32) := [3159351,75826451,6963971,4395795,13751,0x7c058593,6653363,33898115,42286851,64335907,65385507,6935315,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh2 : List (BitVec 32) := [3163447,0xe4850513,17847,0x52058593,1591,361104915,0xb91ff0ef]
def cRow2 : List (BitVec 32) := [7035283,66714003,3774995,19532339]
def cLv20 : List (BitVec 32) := [3163447,0xe0850513,672515,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv21 : List (BitVec 32) := [3163447,0xdc850513,1721091,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv22 : List (BitVec 32) := [3163447,0xd8850513,2769667,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv23 : List (BitVec 32) := [3163447,0xd4850513,3818243,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv24 : List (BitVec 32) := [3163447,0xd0850513,4866819,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv25 : List (BitVec 32) := [3163447,0xcc850513,5915395,4395795,17847,0x3f058593,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh3 : List (BitVec 32) := [3167543,0xa8850513,21943,285574547,1591,361104915,0x93dff0ef]
def cRow3 : List (BitVec 32) := [66812307,3774995,19532339]
def cLv30 : List (BitVec 32) := [3167543,0xa4850513,672515,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv31 : List (BitVec 32) := [3167543,0xa0850513,1721091,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv32 : List (BitVec 32) := [3167543,0x9c850513,2769667,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv33 : List (BitVec 32) := [3167543,0x98850513,3818243,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv34 : List (BitVec 32) := [3167543,0x94850513,4866819,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv35 : List (BitVec 32) := [3167543,0x90850513,5915395,4395795,21943,0xfe058593,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cTail : List (BitVec 32) := [3147063,328979,26039,0xbd058593,343683,8732419,30781475,31831075,17133187,374819,30784547,1049235,1299]
def lvAt (lay j : Nat) : Nat := if lay = 1 then 42247 + 23 * j else if lay = 2 then 42419 + 23 * j else 42567 + 23 * j
def cLvs : List (List (BitVec 32)) := [cLv10, cLv11, cLv12, cLv13, cLv14, cLv15, cLv16, cLv20, cLv21, cLv22, cLv23, cLv24, cLv25, cLv30, cLv31, cLv32, cLv33, cLv34, cLv35]
def lvIdx (lay j : Nat) : Nat := if lay = 1 then j else if lay = 2 then 7 + j else 13 + j
def cLv (lay j : Nat) : List (BitVec 32) := cLvs.getD (lvIdx lay j) []
def regAt (k : Nat) : Nat := 42161 + 7 * (8 - k)
def cRegs : List (List (BitVec 32)) := [cReg0, cReg1, cReg2, cReg3, cReg4, cReg5, cReg6, cReg7, cReg8]
def cReg (k : Nat) : List (BitVec 32) := cRegs.getD k []
section code
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
theorem code_cSnap : CodeAt im (pcOf 42142) cSnap := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cZero2 : CodeAt im (pcOf 42149) cZero2 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHdr : CodeAt im (pcOf 42154) cHdr := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cTop : CodeAt im (pcOf 42224) cTop := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cIdx : CodeAt im (pcOf 42231) cIdx := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCh1 : CodeAt im (pcOf 42235) cCh1 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRow1 : CodeAt im (pcOf 42242) cRow1 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCh2 : CodeAt im (pcOf 42408) cCh2 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRow2 : CodeAt im (pcOf 42415) cRow2 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCh3 : CodeAt im (pcOf 42557) cCh3 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRow3 : CodeAt im (pcOf 42564) cRow3 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cTail : CodeAt im (pcOf 42705) cTail := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_ecall : CodeAt im (pcOf 42718) [0x73] := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cReg (k : Nat) (hk : k < 9) : CodeAt im (pcOf (regAt k)) (cReg k) := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cLv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < (if lay = 1 then 7 else 6)) :
    CodeAt im (pcOf (lvAt lay j)) (cLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
end code
sym_block RSnap := symRun cfgC cSnap (pcOf 42142) 40
sym_block RZero2 := symRun cfgC cZero2 (pcOf 42149) 40
sym_block RHdr := symRun cfgC cHdr (pcOf 42154) 40
sym_block RTop := symRun cfgC cTop (pcOf 42224) 40
sym_block RIdx := symRun cfgC cIdx (pcOf 42231) 40
sym_block RCh1 := symRun cfgC cCh1 (pcOf 42235) 40
sym_block RRow1 := symRun cfgC cRow1 (pcOf 42242) 40
sym_block RCh2 := symRun cfgC cCh2 (pcOf 42408) 40
sym_block RRow2 := symRun cfgC cRow2 (pcOf 42415) 40
sym_block RCh3 := symRun cfgC cCh3 (pcOf 42557) 40
sym_block RRow3 := symRun cfgC cRow3 (pcOf 42564) 40
sym_block RTail := symRun cfgC cTail (pcOf 42705) 40
sym_block RReg0 := symRun cfgC (cReg 0) (pcOf (regAt 0)) 40
sym_block RReg1 := symRun cfgC (cReg 1) (pcOf (regAt 1)) 40
sym_block RReg2 := symRun cfgC (cReg 2) (pcOf (regAt 2)) 40
sym_block RReg3 := symRun cfgC (cReg 3) (pcOf (regAt 3)) 40
sym_block RReg4 := symRun cfgC (cReg 4) (pcOf (regAt 4)) 40
sym_block RReg5 := symRun cfgC (cReg 5) (pcOf (regAt 5)) 40
sym_block RReg6 := symRun cfgC (cReg 6) (pcOf (regAt 6)) 40
sym_block RReg7 := symRun cfgC (cReg 7) (pcOf (regAt 7)) 40
sym_block RReg8 := symRun cfgC (cReg 8) (pcOf (regAt 8)) 40
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
  0x300000 + 8136 + 64 * ((if lay = 1 then 66 else if lay = 2 then 116 else 165) + (if lay = 1 then 6 else 5) - j)
def lvDst (lay : Nat) : Nat := 0x800 + (if lay = 1 then 12224 else if lay = 2 then 15344 else 18400)
def lvH (lay : Nat) : Nat := if lay = 1 then 7 else 6
def rLvs : List Result := [RLv10.res, RLv11.res, RLv12.res, RLv13.res, RLv14.res, RLv15.res, RLv16.res, RLv20.res,
  RLv21.res, RLv22.res, RLv23.res, RLv24.res, RLv25.res, RLv30.res, RLv31.res, RLv32.res, RLv33.res, RLv34.res,
  RLv35.res]
def rLv (lay j : Nat) : Result := rLvs.getD (lvIdx lay j) RLv10.res
theorem rLv_eq (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay) :
    rLv lay j = ⟨⟨lvRegs j (lvSrc lay j) (lvDst lay), lvMem j (lvSrc lay j) (lvDst lay),
      lvObl j (lvSrc lay j) (lvDst lay)⟩, .c (pcOf (lvAt lay j + 23)), .endOfCode, 23, 23⟩ := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
theorem run_lv (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay) :
    symRun cfgC (cLv lay j) (pcOf (lvAt lay j)) 40 = some (rLv lay j) := by
  obtain ⟨h1, h4⟩ := hl
  unfold lvH at hj
  interval_cases lay <;> simp only [if_true, if_false, show (2 : Nat) ≠ 1 by decide, show (3 : Nat) ≠ 1 by decide] at hj <;>
    interval_cases j <;> kernel_rfl
def LPLAN : Nat := 0xff9400
def LPlanAt (t : MachineState) : Prop :=
  ∀ k < 192, t.getMem (BitVec.ofNat 64 (LPLAN + 8 * k)) = bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * k)).take 8)
def lvRow (lay r : Nat) : Nat := if lay = 1 then 64 + r else r
set_option maxRecDepth 100000 in
theorem lplan1_ok : ∀ r < 128, ∀ j < 7,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * (64 + r))).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.T3M.lowerPlan 1 r).getD j 0) := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lplan2_ok : ∀ r < 64, ∀ j < 6,
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * r)).take 8)) j =
      BitVec.ofNat 64 ((ClaudeWCT.W9.T3M.lowerPlan 2 r).getD j 0) ∧
    (ClaudeWCT.W9.T3M.lowerPlan 3 r).getD j 0 = (ClaudeWCT.W9.T3M.lowerPlan 2 r).getD j 0 := by
  decide +kernel
set_option maxRecDepth 100000 in
theorem lowerPlan_lt : (∀ r < 128, ∀ j < 7, (ClaudeWCT.W9.T3M.lowerPlan 1 r).getD j 0 + 4 ≤ 23) ∧
    (∀ r < 64, ∀ j < 6, (ClaudeWCT.W9.T3M.lowerPlan 2 r).getD j 0 + 4 ≤ 19) := by
  decide +kernel
def plan (lay r j : Nat) : Nat := (ClaudeWCT.W9.T3M.lowerPlan (Fin.ofNat 4 lay) r).getD j 0
theorem plan_ok (lay r j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hr : r < 2 ^ lvH lay) (hj : j < lvH lay) :
    LoadKind.bu.fromWord (bytesToWordLE ((ClaudeWCT.W9.Machine.Expand.lplanBytes.drop (8 * lvRow lay r)).take 8)) j =
      BitVec.ofNat 64 (plan lay r j) ∧ plan lay r j + 4 ≤ (if lay = 1 then 23 else 19) := by
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem lv_spec (lay j : Nat) (hl : 1 ≤ lay ∧ lay < 4) (hj : j < lvH lay) (s : MachineState)
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
  have hH := lvH_le lay
  have hr7 : r < 2 ^ 7 := lt_of_lt_of_le hr (Nat.pow_le_pow_right (by norm_num) hH)
  have hj7 : j < 7 := by omega
  have ht6 := t6E_eval h19 hr7 j hj7
  have hpb := pbE_eval hl hr h20 hp j hj
  have hpl := (plan_ok lay r j hl hr hj).2
  have hpl23 : plan lay r j ≤ 23 := by split_ifs at hpl <;> omega
  have hb : r / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨h1, h4⟩ := hl
  have hD : lvDst lay + 16 * 23 ≤ 0x800 + 21488 ∧ 0x800 + 12224 ≤ lvDst lay := by
    unfold lvDst; split_ifs <;> omega
  have hDp : lvDst lay + 16 * plan lay r j + 64 ≤ 0x800 + 21488 := by
    unfold lvDst at *; split_ifs at * <;> omega
  have hS : 0x300000 + 8136 + 64 * 66 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x300000 + 21832 := by
    unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
  have hS16 : lvSrc lay j % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 16 = 0 := by unfold lvDst; split_ifs <;> omega
  have hrun := run_lv lay j ⟨h1, h4⟩ hj
  rw [rLv_eq lay j ⟨h1, h4⟩ hj] at hrun
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
