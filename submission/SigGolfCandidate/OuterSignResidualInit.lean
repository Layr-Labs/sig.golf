import SigGolfCandidate.OuterInstalledPool
import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignResidualInit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Search SigGolfCandidate.T3M.Sign.SharedControlTail
theorem initResidual_steps {im : Image} (hc : CodeAt im (pcOf 22226) initResidualCode)
    (hg : CodeAt im (pcOf 1970) OuterRoutePool.signCode)
    (s : MachineState) (hp : s.pc=pcOf 22226) (leaf : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t,Steps im s 12 12 t ∧ t.pc=pcOf 22230 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (OuterSigning.rootPool leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A => A=0x66008) := by
  obtain ⟨u,su,pu,ru,fu⟩ := SigGolfCandidate.T3M.Search.T51.jump_hook (k:=22226) (t:=1970)
    (off:=18446744073709470592) (fun _=>rfl) hc (by norm_num [pcOf])
    (by norm_num [pcOf]) (by norm_num [pcOf]) s hp
  obtain ⟨t,ut,pt,tm,rt,ft⟩ := OuterRoutePool.sign_steps hg u pu leaf hl ((ru.get (by decide)).trans h18)
  refine ⟨t,su.trans ut,pt,?_,(ru.trans rt).mono (by decide),(fu.trans ft).mono (by simp)⟩
  change t.getMem (0x66008#64)=BitVec.ofNat 64 (OuterSigning.rootPool leaf)
  exact tm


theorem installed (s : MachineState) (hp : s.pc=pcOf 22226) (leaf : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t,Steps OuterImages.signImage s 12 12 t ∧ t.pc=pcOf 22230 ∧
      t.getMem (0x66008#64)=BitVec.ofNat 64 (OuterSigning.rootPool leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A=>A=0x66008) :=
  initResidual_steps (OuterSignTransfers.code (b:=22226) (words:=initResidualCode) (by decide +kernel)
    SigGolfCandidate.T3M.Sign.SharedControlTail.installed_initResidual) OuterInstalledPool.sign s hp leaf hl h18
#print axioms installed
end OuterSignResidualInit
