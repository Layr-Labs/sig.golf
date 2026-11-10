import SigGolfCandidate.AllRouteClamp
import SigGolfCandidate.AllRouteDispatch
set_option debug.skipKernelTC false
namespace SigGolfCandidate.T3M.AllRouteHelpers
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option linter.all false
def signRawCode : List (BitVec 32) := [0x40730333]
sym_block signRaw := symRun {noAlias:=true} signRawCode (pcOf 25901) 2
 theorem signRaw_steps {image : Image} (hc : CodeAt image (pcOf 25901) signRawCode)
    (s : MachineState) (hp : s.pc=pcOf 25901) (r c : Nat) (hr : r<2^32) (hc' : c ≤ r)
    (h6 : s.getReg .x6=BitVec.ofNat 64 r) (h7 : s.getReg .x7=BitVec.ofNat 64 c) :
    ∃ t, Steps image s 1 1 t ∧ t.pc=pcOf 25902 ∧ t.getReg .x6=BitVec.ofNat 64 (r-c) ∧
      RegsExcept s t [.x6] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound signRaw hc s hp (by simp [signRaw.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · simp only [Result.toState_getReg,signRaw.res]; t3n [h6,h7]
    exact BitVec.ofNat_sub_ofNat_of_le r c (by omega) hc'
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
 def signRestoreCode : List (BitVec 32) := [0x66e37,0x9adfc06f]
sym_block signRestore := symRun {noAlias:=true} signRestoreCode (pcOf 25932) 3
 theorem signRestore_steps {image : Image} (hc : CodeAt image (pcOf 25932) signRestoreCode)
    (s : MachineState) (hp : s.pc=pcOf 25932) :
    ∃ t, Steps image s 2 2 t ∧ t.pc=pcOf 22456 ∧ t.getReg .x28=BitVec.ofNat 64 0x66000 ∧
      RegsExcept s t [.x28] ∧ Frame s t (fun _=>False) := by
  refine ⟨_,symRun_sound signRestore hc s hp (by simp [signRestore.res,rv_simp]),?_,?_,?_,?_⟩
  · rfl
  · rfl
  · intro q hq; cases q <;> simp at hq <;> rfl
  · intro A hA hn; rfl
#print axioms signRaw_steps
#print axioms signRestore_steps
end SigGolfCandidate.T3M.AllRouteHelpers
