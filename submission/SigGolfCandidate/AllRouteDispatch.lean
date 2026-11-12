import SigGolfCandidate.AllRoutePureHelpers
import SigGolfCandidate.AllRouteSavings
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.AllRoute SigGolfCandidate.T3M.AllRoutePath
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option linter.all false
def signDispatchOneCode : List (BitVec 32) := bv_list% 32 [0x40730333,0xfff40393,0x4039a63,0x696973b7,0x96938393,0x6097e13,0xfa0e0e13,0xe1663,0x54000e37,0x41c383b3,0x2039393,0x69697e37,0x969e0e13,0x1c383b3,0x6097e13,0xe1463,0xfeb38393,0x1f97e13,0x1e1e13,0x1c3d3b3,0x33f393,0x1c0006f,0x13,0xffe40393,0x39e63,0x195393,0x123c3b3,0x13f393,0x40730333,0x35463,0x313,0x66e37,0xe18fc06f]
def signDispatchOneKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def signDispatchOnePost (leaf : Nat) : List (Reg × Word) :=
  [(.x7,BitVec.ofNat 64 (lowerSave 1 leaf)),(.x18,BitVec.ofNat 64 leaf),(.x8,BitVec.ofNat 64 1)]
def signDispatchOneRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 26130 signDispatchOneCode) [pcOf 26158] 50 (pcOf 26131) []
    (σK [(.x18,BitVec.ofNat 64 leaf),(.x8,BitVec.ofNat 64 1)]) []
def signDispatchOneCheck (leaf : Nat) : Bool := pureCheck (signDispatchOneRun leaf) (signDispatchOnePost leaf) signDispatchOneKeep 26158 24
 theorem signDispatchOne_checked : ∀ leaf : Fin 128, signDispatchOneCheck leaf.val = true := by decide +kernel
 theorem signDispatchOne_steps {image : Image} (hc : CodeAt image (pcOf 26130) signDispatchOneCode)
    (s : MachineState) (hp : s.pc=pcOf 26131) (leaf : Fin 128)
    (hLeaf : s.getReg .x18=BitVec.ofNat 64 leaf.val)
    (hLay : s.getReg .x8=BitVec.ofNat 64 1) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 26158 ∧
      t.getReg .x7=BitVec.ofNat 64 (lowerSave 1 leaf.val) ∧
      RegsExcept s t [.x7,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 26130).toNat = 4096+4*26130) hc
  have hcheck := signDispatchOne_checked leaf
  unfold signDispatchOneCheck signDispatchOneRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact hLeaf
    · exact hLay)
  refine ⟨t,n,st,hn,hpc,hpost (.x7,BitVec.ofNat 64 (lowerSave 1 leaf.val)) (by simp [signDispatchOnePost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x18,BitVec.ofNat 64 leaf.val) (by simp [signDispatchOnePost])).trans hLeaf.symm
  | exact (hpost (.x8,BitVec.ofNat 64 1) (by simp [signDispatchOnePost])).trans hLay.symm
  | rfl
#print axioms signDispatchOne_steps
def signDispatchTwoCode : List (BitVec 32) := bv_list% 32 [0x40730333,0xfff40393,0x4039a63,0x696973b7,0x96938393,0x6097e13,0xfa0e0e13,0xe1663,0x54000e37,0x41c383b3,0x2039393,0x69697e37,0x969e0e13,0x1c383b3,0x6097e13,0xe1463,0xfeb38393,0x1f97e13,0x1e1e13,0x1c3d3b3,0x33f393,0x1c0006f,0x13,0xffe40393,0x39e63,0x195393,0x123c3b3,0x13f393,0x40730333,0x35463,0x313,0x66e37,0xe18fc06f]
def signDispatchTwoKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def signDispatchTwoPost (leaf : Nat) : List (Reg × Word) :=
  [(.x7,BitVec.ofNat 64 (lowerSave 2 leaf)),(.x18,BitVec.ofNat 64 leaf),(.x8,BitVec.ofNat 64 2)]
def signDispatchTwoRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 26130 signDispatchTwoCode) [pcOf 26158] 50 (pcOf 26131) []
    (σK [(.x18,BitVec.ofNat 64 leaf),(.x8,BitVec.ofNat 64 2)]) []
def signDispatchTwoCheck (leaf : Nat) : Bool := pureCheck (signDispatchTwoRun leaf) (signDispatchTwoPost leaf) signDispatchTwoKeep 26158 24
 theorem signDispatchTwo_checked : ∀ leaf : Fin 64, signDispatchTwoCheck leaf.val = true := by decide +kernel
 theorem signDispatchTwo_steps {image : Image} (hc : CodeAt image (pcOf 26130) signDispatchTwoCode)
    (s : MachineState) (hp : s.pc=pcOf 26131) (leaf : Fin 64)
    (hLeaf : s.getReg .x18=BitVec.ofNat 64 leaf.val)
    (hLay : s.getReg .x8=BitVec.ofNat 64 2) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 26158 ∧
      t.getReg .x7=BitVec.ofNat 64 (lowerSave 2 leaf.val) ∧
      RegsExcept s t [.x7,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 26130).toNat = 4096+4*26130) hc
  have hcheck := signDispatchTwo_checked leaf
  unfold signDispatchTwoCheck signDispatchTwoRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact hLeaf
    · exact hLay)
  refine ⟨t,n,st,hn,hpc,hpost (.x7,BitVec.ofNat 64 (lowerSave 2 leaf.val)) (by simp [signDispatchTwoPost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x18,BitVec.ofNat 64 leaf.val) (by simp [signDispatchTwoPost])).trans hLeaf.symm
  | exact (hpost (.x8,BitVec.ofNat 64 2) (by simp [signDispatchTwoPost])).trans hLay.symm
  | rfl
#print axioms signDispatchTwo_steps
end SigGolfCandidate.T3M.AllRouteHelpers
