import SigGolfCandidate.OuterSigning
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
namespace OuterRoutePool
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
/-- C39: the sign root-pool jump (1970) and its relocated block (26415). -/
abbrev SignAt (im : Image) : Prop := TopRoutePool.SignAt im
/-- C39: the expand root-pool jump (54324) and its relocated block (88400). -/
abbrev ExpandAt (im : Image) : Prop := TopRoutePool.ExpandAt im
theorem sign_steps {im : Image} (hc : SignAt im)
    (s : MachineState) (hp : s.pc=pcOf 1970) (leaf : Nat) (hl : leaf<4096)
    (h18 : s.getReg .x18=BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s 47 47 t ∧ t.pc=pcOf 22230 ∧
      t.getMem 0x66008=BitVec.ofNat 64 (OuterSigning.rootPool leaf) ∧
      RegsExcept s t [.x6,.x28] ∧ Frame s t (fun A=>A=0x66008) :=
  SigGolfCandidate.Route16Machine.signPool_steps hc.1 hc.2 s hp leaf hl h18
theorem expandIndex_steps {im : Image} (hc : ExpandAt im)
    (s : MachineState) (hp : s.pc=pcOf 54324) (index H : Nat) (hi : index<2^31)
    (hmidx : s.getMem 0x20550=BitVec.ofNat 64 index) (hm : s.getMem 0x66000=BitVec.ofNat 64 H) :
    ∃ t, Steps im s 50 50 t ∧ t.pc=pcOf 46933 ∧
      t.getReg .x21=BitVec.ofNat 64 (OuterSigning.rootPool (index/2^19)) ∧
      t.getReg .x20=BitVec.ofNat 64 H ∧ RegsExcept s t [.x20,.x21,.x28] ∧ Frame s t (fun _=>False) :=
  SigGolfCandidate.Route16Machine.expandPool_steps hc.1 hc.2 s hp index H hi hmidx hm
end OuterRoutePool
#print axioms OuterRoutePool.sign_steps
#print axioms OuterRoutePool.expandIndex_steps
