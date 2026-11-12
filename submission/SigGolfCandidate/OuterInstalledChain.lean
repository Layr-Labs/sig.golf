import SigGolfCandidate.OuterChainBank
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledChain
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine

theorem window : (Frozen.image.code.drop 195584).take 36032=(OuterImages.expandImage.code.drop 195584).take 36032 := by
  have hwin : (Frozen.image.code.drop 195584).take 59072=(Images.expandImage.code.drop 195584).take 59072 := by
    rw [Frozen.image_eq]
    exact Images.expand_banks_eq_verify.symm
  have h:=congrArg (List.take 36032) hwin
  simp only [List.take_take,show min 36032 59072=36032 from rfl] at h
  exact h.trans (OuterImageWindows.high_window 195584 36032 (by decide) (by decide)).symm

#print axioms window
end OuterInstalledChain
