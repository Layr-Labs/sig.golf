import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.CompactCode
import SigGolfCandidate.ClaudeWCT.W9.T3M.Witness.Layout

section

namespace ClaudeWCT.W9.Machine.Expand.Compact2
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Expand.Compact (cfgC)
def cSnap : List (BitVec 32) := [5431,0x80050513,3147191,361875,5687,0xaa960613,0xfb9ff0ef]
def cZero2 : List (BitVec 32) := [1463,1275430291,5687,2632320531,4229951727]  -- nested FTS: zero 2718 words from 1216
/-- Nested FTS (r1-1): the header copy is replaced by `jal zero,P_final` (P_final at words 33117..33284). -/
def cHdr : List (BitVec 32) := [2899275887]
def cCtr : List (BitVec 32) := [3147063,33883411,1308624275,2098707,1280344303]
def cPRegs : List (List (BitVec 32)) := [[3147063,67437843,9655,386237843,117442067,1255178479],[3147063,1006961939,9655,3741681043,117442067,1230012655],[3147063,1946486035,9655,2802156947,117442067,1204846831],[3151159,2886010131,5559,1862632851,117442067,1179681007],[3151159,3825534227,5559,923108755,117442067,1154515183],[3151159,470091027,5559,4278551955,117442067,1129349359],[3151159,1409615123,5559,3339027859,117442067,1104183535],[3155255,2349139219,5559,2399503763,117442067,1079017711],[3155255,3288663315,1463,1459979667,117442067,1053851887]]
def cHolds : List (List (BitVec 32)) := [[3673655,17710979,933507,9322243,8361619,5218195,32933555,9015,201523987,6719155,30847011,31896611],[3673655,51265411,34487939,42876675,8361619,5218195,32933555,9015,3556967187,6719155,30847011,31896611],[3673655,84819843,68042371,76431107,8361619,5218195,32933555,9015,2617443091,6719155,30847011,31896611],[3673655,118374275,101596803,109985539,8361619,5218195,32933555,4919,1677918995,6719155,30847011,31896611],[3673655,151928707,135151235,143539971,8361619,5218195,32933555,4919,738394899,6719155,30847011,31896611],[3673655,185483139,168705667,177094403,8361619,5218195,32933555,4919,4093838099,6719155,30847011,31896611],[3673655,219037571,202260099,210648835,8361619,5218195,32933555,4919,3154314003,6719155,30847011,31896611],[3673655,252592003,235814531,244203267,8361619,5218195,32933555,4919,2214789907,6719155,30847011,31896611],[3673655,286146435,269368963,277757699,8361619,5218195,32933555,823,1275265811,6719155,30847011,31896611]]
def cPEnd : List (BitVec 32) := [990937199]
def cPReg (c : Nat) : List (BitVec 32) := cPRegs.getD c []
def cHold (c : Nat) : List (BitVec 32) := cHolds.getD c []
def pregAt (c : Nat) : Nat := 33122 + 6 * c
def holdPc (c : Nat) : Nat := 33176 + 12 * c
def cReg8 : List (BitVec 32) := [3155255,0xc4050513,5559,0x84058593,1591,109446675,0xf6dff0ef]
def cReg7 : List (BitVec 32) := [3155255,0x8c050513,5559,0xb7058593,1591,109446675,0xf51ff0ef]
def cReg6 : List (BitVec 32) := [3151159,0x54050513,5559,0xea058593,1591,109446675,0xf35ff0ef]
def cReg5 : List (BitVec 32) := [3151159,470091027,5559,486901139,1591,109446675,0xf19ff0ef]
def cReg4 : List (BitVec 32) := [3151159,0xe4050513,5559,0x50058593,1591,109446675,0xefdff0ef]
def cReg3 : List (BitVec 32) := [3151159,0xac050513,9655,0x83058593,1591,109446675,0xee1ff0ef]
def cReg2 : List (BitVec 32) := [3147063,0x74050513,9655,0xb6058593,1591,109446675,0xec5ff0ef]
def cReg1 : List (BitVec 32) := [3147063,1006961939,9655,0xe9058593,1591,109446675,0xea9ff0ef]
def cReg0 : List (BitVec 32) := [3147063,67437843,9655,470123923,1591,109446675,0xe8dff0ef]
def cTop : List (BitVec 32) := [3155255,0xfc850513,9655,0x50058593,1591,554042899,0xe71ff0ef]
def cIdx : List (BitVec 32) := [0x6003b03,35347219,0xff9937,0x40090913]
def cCh1 : List (BitVec 32) := [3159351,545588499,13751,1896187283,1591,361104915,3831492847]
def cRow1 : List (BitVec 32) := [0xcb5993,0x7f9f993,3774995,19532339,537528851]
def cLv10 : List (BitVec 32) := [3159351,478479635,672515,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv11 : List (BitVec 32) := [3159351,411370771,1721091,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv12 : List (BitVec 32) := [3159351,344261907,2769667,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv13 : List (BitVec 32) := [3159351,277153043,3818243,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv14 : List (BitVec 32) := [3159351,210044179,4866819,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv15 : List (BitVec 32) := [3159351,142935315,5915395,4395795,13751,1476756883,6653363,33898115,42286851,64335907,65385507,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv16 : List (BitVec 32) := [3159351,75826451,6963971,4395795,13751,1476756883,6653363,33898115,42286851,64335907,243273839,6935315,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh2 : List (BitVec 32) := [3163447,3833922835,17847,822445459,1591,361104915,3105878255]
def cRow2 : List (BitVec 32) := [7035283,66714003,3774995,19532339]
def cLv20 : List (BitVec 32) := [3163447,3766813971,672515,4395795,17847,486901139,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv21 : List (BitVec 32) := [3163447,3699705107,1721091,4395795,17847,486901139,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv22 : List (BitVec 32) := [3163447,3632596243,2769667,4395795,17847,486901139,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv23 : List (BitVec 32) := [3163447,3565487379,3818243,4395795,17847,486901139,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv24 : List (BitVec 32) := [3163447,3498378515,4866819,4395795,17847,486901139,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv25 : List (BitVec 32) := [3163447,3431269651,5915395,4395795,17847,486901139,6653363,33898115,42286851,64335907,1783627887,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cCh3 : List (BitVec 32) := [3167543,2827289875,21943,4043670931,1591,361104915,2480926959]
def cRow3 : List (BitVec 32) := [66812307,3774995,19532339]
def cLv30 : List (BitVec 32) := [3167543,2760181011,672515,4395795,21943,3708126611,6653363,33898115,42286851,64335907,65385507,643859,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv31 : List (BitVec 32) := [3167543,2693072147,1721091,4395795,21943,3708126611,6653363,33898115,42286851,64335907,65385507,1692435,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv32 : List (BitVec 32) := [3167543,2625963283,2769667,4395795,21943,3708126611,6653363,33898115,42286851,64335907,65385507,2741011,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv33 : List (BitVec 32) := [3167543,2558854419,3818243,4395795,21943,3708126611,6653363,33898115,42286851,64335907,65385507,3789587,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv34 : List (BitVec 32) := [3167543,2491745555,4866819,4395795,21943,3708126611,6653363,33898115,42286851,64335907,65385507,4838163,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cLv35 : List (BitVec 32) := [3167543,2424636691,5915395,4395795,21943,3708126611,6653363,33898115,42286851,64335907,1179648111,5886739,1274643,1262355,5444499,4395795,7537459,6620467,6653363,343683,8732419,30781475,31831075]
def cTail : List (BitVec 32) := [3147063,328979,26039,2634384787,343683,8732419,30781475,31831075,17133187,374819,30784547]
def lvAt (lay j : Nat) : Nat := if lay = 1 then 42247 + 23 * j else if lay = 2 then 42419 + 23 * j else 42567 + 23 * j
def cLvs : List (List (BitVec 32)) := [cLv10, cLv11, cLv12, cLv13, cLv14, cLv15, cLv16, cLv20, cLv21, cLv22, cLv23, cLv24, cLv25, cLv30, cLv31, cLv32, cLv33, cLv34, cLv35]
def lvIdx (lay j : Nat) : Nat := if lay = 1 then j else if lay = 2 then 7 + j else 13 + j
def cLv (lay j : Nat) : List (BitVec 32) := cLvs.getD (lvIdx lay j) []
def regAt (k : Nat) : Nat := 42161 + 7 * (8 - k)
def cRegs : List (List (BitVec 32)) := [cReg0, cReg1, cReg2, cReg3, cReg4, cReg5, cReg6, cReg7, cReg8]
def cReg (k : Nat) : List (BitVec 32) := cRegs.getD k []
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
include hc
theorem code_cSnap : CodeAt im (pcOf 42142) cSnap := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cZero2 : CodeAt im (pcOf 42149) cZero2 := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHdr : CodeAt im (pcOf 42154) cHdr := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cTop : CodeAt im (pcOf 42224) cTop := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCtr : CodeAt im (pcOf 33117) cCtr := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cPEnd : CodeAt im (pcOf 33284) cPEnd := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cPReg (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (pregAt c)) (cPReg c) := by
  interval_cases c <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHold (c : Nat) (hc9 : c < 9) : CodeAt im (pcOf (holdPc c)) (cHold c) := by
  interval_cases c <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
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
theorem code_cLvA (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (lvAt lay (rootJ lay))) (cLvA lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cLvB (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) :
    CodeAt im (pcOf (lvAt lay (rootJ lay) + 11)) (cLvB lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRT (lay : Nat) (hl : 1 ≤ lay ∧ lay < 4) : CodeAt im (pcOf (rtAt lay)) (cRT lay) := by
  obtain ⟨h1, h4⟩ := hl
  interval_cases lay <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
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
/-- Lower-layer path area in the final witness (C2 D4: layer bases 11648 / 14800 / 17872). -/
def lvDst (lay : Nat) : Nat := 0x800 + (if lay = 1 then 11648 else if lay = 2 then 14800 else 17872)
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
theorem lowerPlan_lt : (∀ r < 128, ∀ j < 7, (ClaudeWCT.W9.T3M.lowerPlan 1 r).getD j 0 + 4 ≤ 25) ∧
    (∀ r < 64, ∀ j < 6, (ClaudeWCT.W9.T3M.lowerPlan 2 r).getD j 0 + 4 ≤ 20) := by
  decide +kernel
def plan (lay r j : Nat) : Nat := (ClaudeWCT.W9.T3M.lowerPlan (Fin.ofNat 4 lay) r).getD j 0
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
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
  have hS : 0x300000 + 8136 + 64 * 66 ≤ lvSrc lay j ∧ lvSrc lay j + 64 ≤ 0x300000 + 21832 := by
    unfold lvSrc; unfold lvH at hj; split_ifs at * <;> omega
  have hS16 : lvSrc lay j % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 16 = 0 := by unfold lvDst; split_ifs <;> omega
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
variable {im : Image} (hc : ClaudeWCT.W9.Machine.Expand.NewCodeAt im)
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
  have hS : 0x300000 + 8136 + 64 * 66 ≤ lvSrc lay (rootJ lay) ∧ lvSrc lay (rootJ lay) + 64 ≤ 0x300000 + 21832 := by
    unfold lvSrc; unfold lvH at hjl; split_ifs at * <;> omega
  have hS16 : lvSrc lay (rootJ lay) % 16 = 8 := by unfold lvSrc; split_ifs <;> omega
  have hDm : lvDst lay % 16 = 0 := by unfold lvDst; split_ifs <;> omega
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
