import SigGolfCandidate.OuterImageWindows
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledDispatch
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine
open ClaudeWCT.W9.Machine.Expand

theorem window : (OuterImages.expandCode.drop 1).take 54333=(Images.expandCode.drop 1).take 54333 := by
  apply OuterImageWindows.unchanged_window 1 54333 (by decide)
  intro i ha hb w
  unfold OuterImages.expandPatch
  split_ifs <;> try omega
  rfl

theorem bounds : ∀ k : Fin 9,1≤SharedDispatch.start k.val ∧
    SharedDispatch.start k.val+(SharedDispatch.words k.val).length≤54334 := by decide +kernel

theorem code (k : Fin 9) : CodeAt OuterImages.expandImage (pcOf (SharedDispatch.start k.val)) (SharedDispatch.words k.val) :=
  codeAt_of_window_eq (bounds k).1 (bounds k).2 (by decide) window.symm (SharedDispatch.installed_code k)

#print axioms code
end OuterInstalledDispatch
