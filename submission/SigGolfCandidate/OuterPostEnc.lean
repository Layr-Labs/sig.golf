import SigGolfCandidate.OuterPostPass
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPostEnc
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput route)
open ClaudeWCT ClaudeWCT.W9.Machine.Expand.PostPass ClaudeWCT.W9.Machine.Expand.PostEnc
theorem pp_witEnc (s : MachineState) (hpc : s.pc = pcOf 49400) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hF : ∀ j, j < 958 → s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * j) 64)
    (hO : ∀ j, 1012 ≤ j → j < 2905 → j ≠ 2789 →
      s.getMem (BitVec.ofNat 64 (2904 + 8 * j)) = oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * j))
    (hC : s.getMem (BitVec.ofNat 64 (2904 + 8 * 2789)) =
      replaceByte (oldWord output (ClaudeWCT.W9.T3M.Paired.mainWitness w) (8 * 2789)) 0 (ClaudeWCT.W9.Machine.Expand.OldW.choiceByte w.topHigh).toBitVec)
    (hleaf : leafOf (s.getMem (BitVec.ofNat 64 0x20160)) % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096) :
    ∃ t, Steps OuterImages.expandImage s 17535 ppCycles t ∧ t.pc = pcOf 54174 ∧
      RegsExcept s t [.x6, .x7, .x10, .x28, .x29, .x30] ∧
      (∀ k, k < 2720 → t.getMem (BitVec.ofNat 64 (4256 + 8 * k)) = (ClaudeWCT.W9.T3M.Paired.witEnc output w).extractLsb' (64 * k) 64) ∧
      ∀ A < 2 ^ 64, t.getMem (BitVec.ofNat 64 A) =
        ppMem (leafOf (s.getMem (BitVec.ofNat 64 0x20160))) (fun B => s.getMem (BitVec.ofNat 64 B)) A := by
  obtain ⟨t, st, tp, tr, tm⟩ := OuterPostPass.pp_spec s hpc
  refine ⟨t, st, tp, tr, fun k hk => ?_, tm⟩
  rw [tm (4256 + 8 * k) (by omega)]
  exact ppMem_witEnc output w (fun B => s.getMem (BitVec.ofNat 64 B)) hF hO hC hleaf k hk


#print axioms pp_witEnc
end OuterPostEnc
