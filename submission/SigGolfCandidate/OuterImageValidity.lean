import SigGolfCandidate.OuterValidityLengths
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterImageValidity
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M

def images : Phase→Image
  | .keygen=>Images.keygenImage
  | .sign=>OuterImages.signImage
  | .expand=>OuterImages.expandImage
  | .verify=>Images.verifyImage
abbrev sub : Submission:=OuterRuntime.runtimeSub images

theorem sign_raw : OuterImages.signImage.Valid OuterValidityCore.sizes OuterValidityCore.layout := by
  have h:=OuterValidityLengths.valid OuterImages.signImage OuterImages.signCode Images.signData
    rfl rfl 26241 86144 OuterImages.sign_length Images.signData_length (by decide) (by decide)
  exact h

theorem expand_raw : OuterImages.expandImage.Valid OuterValidityCore.sizes OuterValidityCore.layout := by
  have h:=OuterValidityLengths.valid OuterImages.expandImage OuterImages.expandCode Images.expandData
    rfl rfl 254656 29936 OuterImages.expand_length Images.expandData_length (by decide) (by decide)
  exact h

theorem sign : (sub.image .sign).Valid sub.sizes sub.layout := by
  dsimp only [sub,OuterRuntime.runtimeSub,images]
  exact sign_raw

theorem expand : (sub.image .expand).Valid sub.sizes sub.layout := by
  dsimp only [sub,OuterRuntime.runtimeSub,images]
  exact expand_raw
#print axioms sign
#print axioms expand
end OuterImageValidity
