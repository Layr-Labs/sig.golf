import SigGolfCandidate.OuterSignSearchBindings
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignTopLeaf
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.Machine.Sign

theorem topSeed : SharedTopSeed.Code OuterImages.signImage := by
  have old:=SharedTopSeed.installed_code
  expose_sign_code
  close_sign_code
theorem leaf : Sign.SharedLeafCode.Code OuterImages.signImage 1013 := by
  have old:=Sign.SharedLeafCode.installed_code
  expose_sign_code
  close_sign_code
theorem chain : SharedChain.Code OuterImages.signImage := by
  have old:=ClaudeWCT.W9.Machine.Sign.SharedChain.installed_code
  expose_sign_code
  close_sign_code
theorem prefixCode : SharedChain.PrefixCode OuterImages.signImage := by
  have old:=ClaudeWCT.W9.Machine.Sign.SharedChain.installed_prefix_code
  expose_sign_code
  close_sign_code
theorem seed : SharedSeed.Code OuterImages.signImage := by
  have old:=SharedSeed.installed_code
  expose_sign_code
  close_sign_code
theorem seedHook : CodeAt OuterImages.signImage (pcOf 1055) Sign.seedHookCode := by
  have old:=SharedSeed.installed_seed_hook
  exact OuterSignTransfers.code (b:=1055) (by decide +kernel) old
theorem spec : SharedTopLeafP.Spec OuterImages.signImage :=
  SharedTopLeafP.topLeafSpec topSeed leaf chain prefixCode seed seedHook
theorem continuation : Sign.SharedTopContinuation.LeafSpec OuterImages.signImage := spec
#print axioms topSeed
#print axioms leaf
#print axioms chain
#print axioms prefixCode
#print axioms seed
#print axioms seedHook
#print axioms continuation
end OuterSignTopLeaf
