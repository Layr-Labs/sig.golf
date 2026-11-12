import SigGolfCandidate.AllRoutePathSound
import SigGolfCandidate.AllRouteSavings
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.AllRoute SigGolfCandidate.T3M.AllRoutePath
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option exponentiation.threshold 10000000
set_option linter.all false
def signOneCode : List (BitVec 32) := bv_list% 32 [0x40730333,0xfff40393,0x4039a63,0x696973b7,0x96938393,0x6097e13,0xfa0e0e13,0xe1663,0x54000e37,0x41c383b3,0x2039393,0x69697e37,0x969e0e13,0x1c383b3,0x6097e13,0xe1463,0xfeb38393,0x1f97e13,0x1e1e13,0x1c3d3b3,0x33f393,0x1c0006f,0x13,0xffe40393,0x39e63,0x195393,0x123c3b3,0x13f393,0x40730333,0x35463,0x313,0x66e37,0xe18fc06f]
def signOneKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def signOnePost (leaf : Nat) : List (Reg × Word) :=
  [(.x7,BitVec.ofNat 64 (lowerSave 1 leaf)),(.x18,BitVec.ofNat 64 leaf)]
def signOneRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 26130 signOneCode) [pcOf 26158] 50 (pcOf 26133) []
    (σK [(.x18,BitVec.ofNat 64 leaf)]) []
def signOneCheck (leaf : Nat) : Bool := pureCheck (signOneRun leaf) (signOnePost leaf) signOneKeep 26158 24
 theorem signOne_checked : ∀ leaf : Fin 128, signOneCheck leaf.val = true := by decide +kernel
 theorem signOne_steps {image : Image} (hc : CodeAt image (pcOf 26130) signOneCode)
    (s : MachineState) (hp : s.pc=pcOf 26133) (leaf : Fin 128)
    (hLeaf : s.getReg .x18=BitVec.ofNat 64 leaf.val) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 26158 ∧
      t.getReg .x7=BitVec.ofNat 64 (lowerSave 1 leaf.val) ∧
      RegsExcept s t [.x7,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 26130).toNat = 4096+4*26130) hc
  have hcheck := signOne_checked leaf
  unfold signOneCheck signOneRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hLeaf)
  refine ⟨t,n,st,hn,hpc,hpost (.x7,BitVec.ofNat 64 (lowerSave 1 leaf.val)) (by simp [signOnePost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x18,BitVec.ofNat 64 leaf.val) (by simp [signOnePost])).trans hLeaf.symm
  | rfl
#print axioms signOne_steps
def signTwoCode : List (BitVec 32) := bv_list% 32 [0x40730333,0xfff40393,0x4039a63,0x696973b7,0x96938393,0x6097e13,0xfa0e0e13,0xe1663,0x54000e37,0x41c383b3,0x2039393,0x69697e37,0x969e0e13,0x1c383b3,0x6097e13,0xe1463,0xfeb38393,0x1f97e13,0x1e1e13,0x1c3d3b3,0x33f393,0x1c0006f,0x13,0xffe40393,0x39e63,0x195393,0x123c3b3,0x13f393,0x40730333,0x35463,0x313,0x66e37,0xe18fc06f]
def signTwoKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def signTwoPost (leaf : Nat) : List (Reg × Word) :=
  [(.x7,BitVec.ofNat 64 (lowerSave 2 leaf)),(.x18,BitVec.ofNat 64 leaf)]
def signTwoRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 26130 signTwoCode) [pcOf 26158] 50 (pcOf 26155) []
    (σK [(.x18,BitVec.ofNat 64 leaf)]) []
def signTwoCheck (leaf : Nat) : Bool := pureCheck (signTwoRun leaf) (signTwoPost leaf) signTwoKeep 26158 24
 theorem signTwo_checked : ∀ leaf : Fin 64, signTwoCheck leaf.val = true := by decide +kernel
 theorem signTwo_steps {image : Image} (hc : CodeAt image (pcOf 26130) signTwoCode)
    (s : MachineState) (hp : s.pc=pcOf 26155) (leaf : Fin 64)
    (hLeaf : s.getReg .x18=BitVec.ofNat 64 leaf.val) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 26158 ∧
      t.getReg .x7=BitVec.ofNat 64 (lowerSave 2 leaf.val) ∧
      RegsExcept s t [.x7,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 26130).toNat = 4096+4*26130) hc
  have hcheck := signTwo_checked leaf
  unfold signTwoCheck signTwoRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hLeaf)
  refine ⟨t,n,st,hn,hpc,hpost (.x7,BitVec.ofNat 64 (lowerSave 2 leaf.val)) (by simp [signTwoPost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x18,BitVec.ofNat 64 leaf.val) (by simp [signTwoPost])).trans hLeaf.symm
  | rfl
#print axioms signTwo_steps
def expandOneCode : List (BitVec 32) := bv_list% 32 [0x406a8ab3,0x20e37,0x550e3383,0xc3d393,0x7f3f393,0x69697337,0x96930313,0x603fe13,0xfa0e0e13,0xe1663,0x54000e37,0x41c30333,0x2031313,0x69697e37,0x969e0e13,0x1c30333,0x603fe13,0xe1463,0xfeb30313,0x1f3fe13,0x1e1e13,0x1c35333,0x337313,0x13,0x406a8ab3,0xad463,0xa93,0xd45f606f]
def expandOneKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def expandOnePost (leaf : Nat) : List (Reg × Word) :=
  [(.x6,BitVec.ofNat 64 (lowerSave 1 leaf)),(.x7,BitVec.ofNat 64 leaf)]
def expandOneRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 56320 expandOneCode) [pcOf 56344] 50 (pcOf 56325) []
    (σK [(.x7,BitVec.ofNat 64 leaf)]) []
def expandOneCheck (leaf : Nat) : Bool := pureCheck (expandOneRun leaf) (expandOnePost leaf) expandOneKeep 56344 24
 theorem expandOne_checked : ∀ leaf : Fin 128, expandOneCheck leaf.val = true := by decide +kernel
 theorem expandOne_steps {image : Image} (hc : CodeAt image (pcOf 56320) expandOneCode)
    (s : MachineState) (hp : s.pc=pcOf 56325) (leaf : Fin 128)
    (hLeaf : s.getReg .x7=BitVec.ofNat 64 leaf.val) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 56344 ∧
      t.getReg .x6=BitVec.ofNat 64 (lowerSave 1 leaf.val) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 56320).toNat = 4096+4*56320) hc
  have hcheck := expandOne_checked leaf
  unfold expandOneCheck expandOneRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hLeaf)
  refine ⟨t,n,st,hn,hpc,hpost (.x6,BitVec.ofNat 64 (lowerSave 1 leaf.val)) (by simp [expandOnePost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x7,BitVec.ofNat 64 leaf.val) (by simp [expandOnePost])).trans hLeaf.symm
  | rfl
#print axioms expandOne_steps
def expandTwoCode : List (BitVec 32) := bv_list% 32 [0x406a8ab3,0x20e37,0x550e3383,0x63d393,0x3f3f393,0x13d313,0x734333,0x137313,0x406a8ab3,0xad463,0xa93,0xcc9f606f]
def expandTwoKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x29,.x30,.x31]
def expandTwoPost (leaf : Nat) : List (Reg × Word) :=
  [(.x6,BitVec.ofNat 64 (lowerSave 2 leaf)),(.x7,BitVec.ofNat 64 leaf)]
def expandTwoRun (leaf : Nat) : Option PRes :=
  pathAux {noAlias:=true} (lookOf 56384 expandTwoCode) [pcOf 56392] 50 (pcOf 56389) []
    (σK [(.x7,BitVec.ofNat 64 leaf)]) []
def expandTwoCheck (leaf : Nat) : Bool := pureCheck (expandTwoRun leaf) (expandTwoPost leaf) expandTwoKeep 56392 24
 theorem expandTwo_checked : ∀ leaf : Fin 64, expandTwoCheck leaf.val = true := by decide +kernel
 theorem expandTwo_steps {image : Image} (hc : CodeAt image (pcOf 56384) expandTwoCode)
    (s : MachineState) (hp : s.pc=pcOf 56389) (leaf : Fin 64)
    (hLeaf : s.getReg .x7=BitVec.ofNat 64 leaf.val) :
    ∃ t n, Steps image s n n t ∧ n≤24 ∧ t.pc=pcOf 56392 ∧
      t.getReg .x6=BitVec.ofNat 64 (lowerSave 2 leaf.val) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 56384).toNat = 4096+4*56384) hc
  have hcheck := expandTwo_checked leaf
  unfold expandTwoCheck expandTwoRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hLeaf)
  refine ⟨t,n,st,hn,hpc,hpost (.x6,BitVec.ofNat 64 (lowerSave 2 leaf.val)) (by simp [expandTwoPost]),?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x7,BitVec.ofNat 64 leaf.val) (by simp [expandTwoPost])).trans hLeaf.symm
  | rfl
#print axioms expandTwo_steps
end SigGolfCandidate.T3M.AllRouteHelpers
