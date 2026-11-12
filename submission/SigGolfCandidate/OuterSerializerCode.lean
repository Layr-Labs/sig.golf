import SigGolfCandidate.OuterSerializer
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSerializerCode
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Sign.SharedSerializer

theorem code : OuterSerializer.Code OuterImages.signImage := by
  have old:=installed_code
  have pre : CodeAt Images.signImage (pcOf 25930) (packWords2.take 33) :=
    SigGolfCandidate.FtsGrind.codeAt_sub 0 old.pack2 (by decide +kernel) rfl
  expose_sign_code
  close_sign_code
#print axioms code
end OuterSerializerCode
