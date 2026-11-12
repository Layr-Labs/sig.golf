import SigGolfCandidate.AllRouteClamp
import SigGolfCandidate.AllRoutePureHelpers
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.T3
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.all false
def expandOneRawCode : List (BitVec 32) := [0x406a8ab3,0x20e37,0x550e3383,0xc3d393,0x7f3f393]
sym_block expandOneRaw := symRun {noAlias:=true} expandOneRawCode (pcOf 56320) 6
 theorem expandOneLeaf_word (index : Nat) (hi : index<2^31) :
    (BitVec.ofNat 64 index >>> 12) &&& 127#64 = BitVec.ofNat 64 (index/2^12%2^7) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show index<2^64 by omega)]
  change (index/2^12) &&& (2^7-1) = (index/2^12%2^7)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (by omega : index/2^12%2^7<2^64)).symm
 theorem expandOneRaw_steps {image : Image} (hc : CodeAt image (pcOf 56320) expandOneRawCode)
    (s : MachineState) (hp : s.pc=pcOf 56320) (index r c : Nat) (hi : index<2^31) (hr : r<2^32) (hcr : c ≤ r)
    (h21 : s.getReg .x21=BitVec.ofNat 64 r) (h6 : s.getReg .x6=BitVec.ofNat 64 c)
    (hm : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 56325 ∧
      t.getReg .x21=BitVec.ofNat 64 (r-c) ∧ t.getReg .x7=BitVec.ofNat 64 (route index 1).1 ∧
      RegsExcept s t [.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hm
  refine ⟨_,symRun_sound expandOneRaw hc s hp (by simp [expandOneRaw.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,expandOneRaw.res]; t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hcr
  · simp only [Result.toState_getReg,expandOneRaw.res]; t3n []
    rw [hm]
    simpa [route,height] using expandOneLeaf_word index hi
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
 def expandOneReturnCode : List (BitVec 32) := [0xd45f606f]
sym_block expandOneReturn := symRun {noAlias:=true} expandOneReturnCode (pcOf 56347) 2
 theorem expandOneReturn_steps {image : Image} (hc : CodeAt image (pcOf 56347) expandOneReturnCode)
    (s : MachineState) (hp : s.pc=pcOf 56347) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46956 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandOneReturn hc s hp (by simp [expandOneReturn.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro q hq; cases q <;> rfl
  · intro A hA hn; rfl
#print axioms expandOneRaw_steps
def expandTwoRawCode : List (BitVec 32) := [0x406a8ab3,0x20e37,0x550e3383,0x63d393,0x3f3f393]
sym_block expandTwoRaw := symRun {noAlias:=true} expandTwoRawCode (pcOf 56384) 6
 theorem expandTwoLeaf_word (index : Nat) (hi : index<2^31) :
    (BitVec.ofNat 64 index >>> 6) &&& 63#64 = BitVec.ofNat 64 (index/2^6%2^6) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and,BitVec.toNat_ushiftRight,BitVec.toNat_ofNat,Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show index<2^64 by omega)]
  change (index/2^6) &&& (2^6-1) = (index/2^6%2^6)%2^64
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact (Nat.mod_eq_of_lt (by omega : index/2^6%2^6<2^64)).symm
 theorem expandTwoRaw_steps {image : Image} (hc : CodeAt image (pcOf 56384) expandTwoRawCode)
    (s : MachineState) (hp : s.pc=pcOf 56384) (index r c : Nat) (hi : index<2^31) (hr : r<2^32) (hcr : c ≤ r)
    (h21 : s.getReg .x21=BitVec.ofNat 64 r) (h6 : s.getReg .x6=BitVec.ofNat 64 c)
    (hm : s.getMem 0x20550=BitVec.ofNat 64 index) :
    ∃ t, Steps image s 5 5 t ∧ t.pc=pcOf 56389 ∧
      t.getReg .x21=BitVec.ofNat 64 (r-c) ∧ t.getReg .x7=BitVec.ofNat 64 (route index 2).1 ∧
      RegsExcept s t [.x7,.x21,.x28] ∧ Frame s t (fun _=>False) := by
  change s.getMem (0x20550#64)=BitVec.ofNat 64 index at hm
  refine ⟨_,symRun_sound expandTwoRaw hc s hp (by simp [expandTwoRaw.res,rv_simp]),?_,?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,expandTwoRaw.res]; t3n [h21,h6]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hcr
  · simp only [Result.toState_getReg,expandTwoRaw.res]; t3n []
    rw [hm]
    simpa [route,height] using expandTwoLeaf_word index hi
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
 def expandTwoReturnCode : List (BitVec 32) := [0xcc9f606f]
sym_block expandTwoReturn := symRun {noAlias:=true} expandTwoReturnCode (pcOf 56395) 2
 theorem expandTwoReturn_steps {image : Image} (hc : CodeAt image (pcOf 56395) expandTwoReturnCode)
    (s : MachineState) (hp : s.pc=pcOf 56395) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 46973 ∧ RegsExcept s t [] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound expandTwoReturn hc s hp (by simp [expandTwoReturn.res,rv_simp]),?_,?_,?_⟩
  · rfl
  · intro q hq; cases q <;> rfl
  · intro A hA hn; rfl
#print axioms expandTwoRaw_steps
end SigGolfCandidate.T3M.AllRouteHelpers
