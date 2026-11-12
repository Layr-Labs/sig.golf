import SigGolfCandidate.OuterImageValidity
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterAdmissible
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.T3M
open OuterImageValidity

theorem keygen_raw : Images.keygenImage.Valid OuterValidityCore.sizes OuterValidityCore.layout := by
  have h:=OuterValidityLengths.valid Images.keygenImage Images.keygenCode Images.keygenData
    rfl rfl 1191 0 Images.keygenCode_length Images.keygenData_length (by decide) (by decide)
  exact h

theorem verify_raw : Images.verifyImage.Valid OuterValidityCore.sizes OuterValidityCore.layout := by
  have h:=OuterValidityLengths.valid Images.verifyImage Images.verifyCode Images.verifyData
    rfl rfl 257258 16928 Images.verifyCode_length Images.verifyData_length (by decide) (by decide)
  exact h

theorem keygen : (sub.image .keygen).Valid sub.sizes sub.layout := by
  dsimp only [sub,OuterRuntime.runtimeSub,images]
  exact keygen_raw

theorem verify : (sub.image .verify).Valid sub.sizes sub.layout := by
  dsimp only [sub,OuterRuntime.runtimeSub,images]
  exact verify_raw

theorem admissible : sub.Admissible := by
  constructor
  · unfold Sizes.Valid
    decide +kernel
  · intro phase
    cases phase
    · exact keygen
    · exact OuterImageValidity.sign
    · exact OuterImageValidity.expand
    · exact verify
#print axioms admissible
end OuterAdmissible
