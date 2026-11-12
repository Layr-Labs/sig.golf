import SigGolfCandidate.OuterForestHalted
import SigGolfCandidate.OuterFrontMemory
import SigGolfCandidate.OuterDigestCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSearched
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def work : Nat := 5173+OuterForestHalted.work

theorem continue_search {sk : BitVec 256} {s0 s : MachineState} {pk : Digest} {b : SharedCodec.CBytes}
    (initial : InitialMemory b pk s0) (hh:(SharedCodec.sigDecC b).policyHints.toNat<12288)
    {r : Option (BitVec 32 × HashOutput)} (hs : SharedFront.Searched s0 b r s) :
    TBSim OuterImages.expandImage sk s work
      (match r with | none=>pure none | some (counter,output)=>OuterForestSuffix.forestProgram output b counter pk) OuterForestHalt.Post := by
  cases r with
  | none =>
    obtain ⟨t,st,tp,t5,t10,regs,frame⟩:=ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary.failure_steps true
      (SharedDigestCode.failure_of_driver OuterTopCodes.driver) s hs.result
    have pc:t.pc=pcOf 45231:=tp
    have hf:fetch OuterImages.expandImage t=some (.base .ECALL):=
      ((SharedDigestCode.failure_ecall_of_driver OuterTopCodes.driver).fetch t pc).trans rfl
    exact (TBSim.steps st (TBSim.pure (Q:=OuterForestHalt.Post) (a:=none)
      ⟨Or.inr pc,t5,t10,hf⟩)).mono (by unfold work OuterForestHalted.work OuterForestSuffix.work OuterSuffix.work; omega) (fun _ _ h=>h)
  | some result =>
    rcases result with ⟨counter,output⟩
    obtain ⟨hp,h19,hc,ha,hout⟩:=hs.result
    have hrank:=((SharedForest.accepted_conditions output ha).2.1)
    obtain ⟨t,st,memory,inv⟩:=OuterFrontMemory.accepted_front initial hs.inflated hh hs.hints hs.frame hs.setupZero hout h19
      hs.resultR17 hp hrank
    exact (TBSim.steps st (OuterForestHalted.halted (sk:=sk) (WCT9.digestIndex_lt output) memory (OuterForestInitial.of_old inv))).mono
      (by unfold work; omega) (fun _ _ h=>h)
#print axioms continue_search
end OuterSearched
