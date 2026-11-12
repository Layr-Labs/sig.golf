import SigGolfCandidate.OuterPadWriter
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterPadWitness
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3
open ClaudeWCT ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired ClaudeWCT.W9.T3M.PairedReadout
open ClaudeWCT.W9.Machine.Expand.PadWriter ClaudeWCT.W9.Machine.Expand.PadWit
theorem pad_hook_witEncG (s : MachineState) (hpc : s.pc = pcOf 54174) (output : HashOutput)
    (w : SigGolfCandidate.Research.SharedForest.Witness)
    (hleaf : (s.getMem (BitVec.ofNat 64 0x66758)).toNat % 4096 = (route (WCT9.digestIndex output) 0).1 % 4096)
    (hn : ∀ j, j < 11 → s.getMem (nonceAddr j) = BitVec.ofNat 64 (w.topNonces.getD j 0))
    (hrec : RecTable s.getMem output w)
    (hbuf : ∀ k, k < 2720 → s.getMem (BitVec.ofNat 64 (4256 + 8 * k)) =
      (Paired.witEnc output w).extractLsb' (64 * k) 64) :
    ∃ t, Steps OuterImages.expandImage s 169 169 t ∧
      t.pc = pcOf 61050 ∧ t.getReg .x10 = 0 ∧
      RegsExcept s t [.x1, .x6, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x18, .x28, .x29, .x30, .x31] ∧
      (∀ k, k < 2720 → t.getMem (BitVec.ofNat 64 (4256 + 8 * k)) = (witEncG output w).extractLsb' (64 * k) 64) ∧
      (∀ A, (∀ j, j < 11 → A ≠ BitVec.ofNat 64 (4256 + noncePos output j)) →
        (∀ e ∈ groundFolds, A ≠ BitVec.ofNat 64 (4256 + lowerNoncePos output e.1 e.2)) → t.getMem A = s.getMem A) := by
  have l1 : (route (WCT9.digestIndex output) 1).1 < 128 := lt_of_lt_of_eq (route_leaf_lt _ 1) (by decide)
  have l2 : (route (WCT9.digestIndex output) 2).1 < 64 := lt_of_lt_of_eq (route_leaf_lt _ 2) (by decide)
  have l3 : (route (WCT9.digestIndex output) 3).1 < 64 := lt_of_lt_of_eq (route_leaf_lt _ 3) (by decide)
  obtain ⟨t, st, tp, t10, rt, mt⟩ := OuterPadWriter.pad_hook s hpc ((route (WCT9.digestIndex output) 1).1 / 2)
    ((route (WCT9.digestIndex output) 2).1 / 2) ((route (WCT9.digestIndex output) 3).1 / 2)
    (by omega) (by omega) (by omega) (hrec 1 (by decide)).2.1 (hrec 2 (by decide)).2.1 (hrec 3 (by decide)).2.1
  refine ⟨t, st, tp, t10, rt, fun k hk => ?_, fun A hA hA' => ?_⟩
  · rw [mt]; exact postPadMem_witEncG s.getMem output w hleaf hn hrec hbuf k hk
  · rw [mt]; exact postPadMem_other s.getMem output w hleaf hrec A hA hA'


#print axioms pad_hook_witEncG
end OuterPadWitness
