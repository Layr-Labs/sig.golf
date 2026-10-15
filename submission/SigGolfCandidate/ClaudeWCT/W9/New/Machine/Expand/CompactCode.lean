import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.Base

namespace ClaudeWCT.W9.Machine.Expand.Compact
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
def cfgC : Config := { noAlias := true }
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
def cSibs : List (List (BitVec 32)) :=[[679427,29658675,647059,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,403095171,411483907,31338531,32388131],[2776579,29658675,1695635,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,335986307,344375043,31338531,32388131],[4873731,29658675,2744211,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,268877443,277266179,31338531,32388131],[6970883,29658675,3792787,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,0xc06be83,0xc86bf03,31338531,32388131],[9068035,29658675,4841363,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,0x806be83,0x886bf03,31338531,32388131],[0xaa5e03,29658675,5889939,2097043,2084755,6264467,5218195,0xdf8fb3,32769715,33426995,67550851,75939587,31338531,32388131],[0xca5e03,29658675,6938515,2084755,6264467,5218195,0xdf8fb3,32769715,441987,8830723,31338531,32388131]]
def cSib (l : Nat) : List (BitVec 32) := cSibs.getD l []
section code
variable {im : Image} (hc : NewCodeAt im)
include hc
theorem code_cStart : CodeAt im (pcOf 41108) cStart := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRegs : CodeAt im (pcOf 41115) cRegs := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cFinal : CodeAt im (pcOf 42120) cFinal := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHalt : CodeAt im (pcOf 42127) cHalt := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cCopy : CodeAt im (pcOf 42130) cCopy := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cZero : CodeAt im (pcOf 42137) cZero := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_copyRet : CodeAt im (pcOf 42136) [0x8067] := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_zeroRet : CodeAt im (pcOf 42141) [0x8067] := codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cHead (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k)) (cHead k) := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cMid (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 6)) (cMid k) := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cRow (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 10)) cRow := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cStep (k : Nat) (hk : k < 9) : CodeAt im (pcOf (coordAt k + 109)) cStep := by
  interval_cases k <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
theorem code_cSib (k l : Nat) (hk : k < 9) (hl : l < 7) : CodeAt im (pcOf (sibAt k l)) (cSib l) := by
  interval_cases k <;> interval_cases l <;> exact codeAt_of_window hc (by decide) (by decide +kernel)
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
sym_block RSib0 := symRun cfgC (cSib 0) (pcOf (sibAt 0 0)) 40
sym_block RSib1 := symRun cfgC (cSib 1) (pcOf (sibAt 0 1)) 40
sym_block RSib2 := symRun cfgC (cSib 2) (pcOf (sibAt 0 2)) 40
sym_block RSib3 := symRun cfgC (cSib 3) (pcOf (sibAt 0 3)) 40
sym_block RSib4 := symRun cfgC (cSib 4) (pcOf (sibAt 0 4)) 40
sym_block RSib5 := symRun cfgC (cSib 5) (pcOf (sibAt 0 5)) 40
sym_block RSib6 := symRun cfgC (cSib 6) (pcOf (sibAt 0 6)) 40
def rSib (l : Nat) : Result := [RSib0.res, RSib1.res, RSib2.res, RSib3.res, RSib4.res, RSib5.res, RSib6.res].getD l RSib0.res
theorem run_sib (k l : Nat) (hk : k < 9) (hl : l < 7) : symRun cfgC (cSib l) (pcOf (sibAt k l)) 40 =
    some ⟨(rSib l).st, .c (pcOf (sibAt k l + sibLen l)), .endOfCode, sibLen l, sibLen l⟩ := by
  interval_cases k <;> interval_cases l <;> kernel_rfl
theorem run_row (k : Nat) (hk : k < 9) : symRun cfgC cRow (pcOf (coordAt k + 10)) 40 =
    some ⟨RRow.res.st, .c (pcOf (coordAt k + 13)), .endOfCode, 3, 3⟩ := by
  interval_cases k <;> kernel_rfl
theorem run_step (k : Nat) (hk : k < 9) : symRun cfgC cStep (pcOf (coordAt k + 109)) 40 =
    some ⟨RStep.res.st, .c (pcOf (coordAt k + 111)), .endOfCode, 2, 2⟩ := by
  interval_cases k <;> kernel_rfl
end ClaudeWCT.W9.Machine.Expand.Compact
