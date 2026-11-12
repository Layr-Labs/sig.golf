import SigGolfCandidate.AllRoutePureHelpers
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify SigGolfCandidate.T3M.AllRoutePath
set_option maxHeartbeats 1000000
set_option linter.all false
 def signThreeKeep : List Reg := [.x1,.x2,.x3,.x4,.x5,.x6,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x16,.x17,.x18,.x19,.x20,.x21,.x22,.x23,.x24,.x25,.x26,.x27,.x28,.x29,.x30,.x31]
def signThreePost : List (Reg × Word) := [(.x8,3)]
def signThreeRun : Option PRes :=
  pathAux {noAlias:=true} (lookOf 26130 signOneCode) [pcOf 26161] 20 (pcOf 26131) [] (σK [(.x8,3)]) []
def signThreeCheck : Bool := pureCheck signThreeRun signThreePost signThreeKeep 26161 4
 theorem signThree_checked : signThreeCheck=true := by decide +kernel
 theorem signThree_steps {image : Image} (hc : CodeAt image (pcOf 26130) signOneCode)
    (s : MachineState) (hp : s.pc=pcOf 26131) (hLay : s.getReg .x8=3) :
    ∃ t n, Steps image s n n t ∧ n≤4 ∧ t.pc=pcOf 26161 ∧
      RegsExcept s t [.x7] ∧ Frame s t (fun _=>False) := by
  have hl := lookOK_of_codeAt (by decide +kernel : (pcOf 26130).toNat=4096+4*26130) hc
  have hcheck := signThree_checked
  unfold signThreeCheck signThreeRun at hcheck
  obtain ⟨t,n,st,hn,hpc,hpost,hkeep,hframe⟩ := pure_run hl hcheck s hp (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hLay)
  refine ⟨t,n,st,hn,hpc,?_,hframe⟩
  intro r hr
  cases r <;> first
  | exact False.elim (hr (by decide))
  | exact hkeep _ (by decide)
  | exact (hpost (.x8,3) (by simp [signThreePost])).trans hLay.symm
  | rfl
#print axioms signThree_steps
end SigGolfCandidate.T3M.AllRouteHelpers
