import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_Base
import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_LayoutCode

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
