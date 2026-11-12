import SigGolfCandidate.OuterLayerRecovery
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLayerFrame
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT OutAt)
open SigGolfCandidate.T3M.Expand (lD lk lWC lWM RlWit CHAIN LEAFPK)
open SigGolfCandidate.T3M.Expand.BC (ltable rlWit_range)
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
theorem not_outer (index A : Nat) (h1 : 0x7f0000 ≤ A) (h2 : A < 0x7f8000) :
    ¬SigGolfCandidate.T3M.Expand.SharedLayers.LW index 4 A := by
  rintro (h|h|⟨lay,_,h|h|h|h⟩)
  · unfold Search.CsW Search.DigW at h;simp only [ENC,EOUT,DIGITS] at h;omega
  · simp only [SigGolfCandidate.T3M.Expand.BC.RlScratch,SigGolfCandidate.T3M.Expand.RlScratch,
      CHAIN,NODE,NOUT,LEAFPK,ENC] at h;omega
  · rcases lD_cases lay with hD|hD|hD|hD <;> omega
  · have:=rlWit_range h;have:=ltable lay;omega
  · rcases h with h|h
    · have:=h.2.2;omega
    · simp only [Search.FLAG] at h;omega
  · unfold SigGolfCandidate.T3M.Expand.RecW at h;omega


#print axioms not_outer
end OuterLayerFrame
