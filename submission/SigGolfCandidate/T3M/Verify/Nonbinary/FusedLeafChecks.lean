import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout
import SigGolfCandidate.T3M.Verify.LayerRuns

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace SigGolfCandidate.T3M
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M.Verify
def keepLfAll (lay : Nat) : List Reg :=
  if lay = 0 then [.x1, .x2, .x7, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x6, .x25, .x26, .x28, .x29, .x31, .x30]
  else [.x1, .x2, .x13, .x19, .x20, .x12, .x21, .x16, .x17, .x8, .x9, .x24, .x22, .x23,
    .x6, .x25, .x26, .x29, .x31, .x30] ++ (if lay = 1 then [] else [.x28])
def fusedLeafCheck (dB dC : Nat) : Bool :=
  specB [] [] baseK (runAt (leafK 0) [] (Nonbinary.pcX 17 dB dC) (lfDirs 0))
    (specLf 0) [] (postLf 0) (keepLfAll 0)
theorem fusedLeafChecks : ((List.range 16).all fun k => fusedLeafCheck (k / 4) (k % 4)) = true := by
  decide +kernel
theorem fusedLeafCheck_at (dB dC : Nat) (hB : dB < 4) (hC : dC < 4) :
    fusedLeafCheck dB dC = true := by
  have h := List.all_eq_true.mp fusedLeafChecks (4*dB+dC) (List.mem_range.mpr (by omega))
  have hd : (4*dB+dC)/4=dB := by omega
  have hm : (4*dB+dC)%4=dC := by omega
  simpa [hd, hm] using h
end SigGolfCandidate.T3M
