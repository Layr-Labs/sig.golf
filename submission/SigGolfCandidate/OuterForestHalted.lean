import SigGolfCandidate.OuterForestHalt
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestHalted
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def work : Nat := OuterForestSuffix.work+OuterSuffix.work

theorem halted {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : OuterForestInv.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)) s) :
    TBSim OuterImages.expandImage sk s work (OuterForestSuffix.forestProgram output b counter pk) OuterForestHalt.Post := by
  have H:=OuterForestSuffix.forest_suffix_good (sk:=sk) hi hm hI
  have H':=TBSim.bind (W₂:=OuterSuffix.work) H (fun r t ht=>OuterForestHalt.finish ht)
  simpa [work] using H'
#print axioms halted
end OuterForestHalted
