import SigGolfCandidate.OuterSignTransfers
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignTrampCode
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind ClaudeWCT.W9.Machine.Sign

theorem s16 : CodeAt OuterImages.signImage (pcOf SIGN_S16) signS16Words :=
  OuterSignTransfers.code (b:=SIGN_S16) (words:=signS16Words) (by decide +kernel) SharedNode.installed_grind.s16

theorem tramp (c : Nat) (hc : c<9) :
    CodeAt OuterImages.signImage (pcOf (SIGN_TRAMP+5*c)) (trampWords (SIGN_TRAMP+5*c) SIGN_S16 (SharedNode.hashPc c+1)) := by
  have hb : ∀ c:Fin 9,OuterSignTransfers.Clean (SIGN_TRAMP+5*c.val)
      (trampWords (SIGN_TRAMP+5*c.val) SIGN_S16 (SharedNode.hashPc c.val+1)).length := by decide +kernel
  have h:=hb ⟨c,hc⟩
  dsimp only at h
  exact OuterSignTransfers.code (b:=SIGN_TRAMP+5*c) h (SharedNode.installed_grind.tramp c hc)
#print axioms s16
#print axioms tramp
end OuterSignTrampCode
