import SigGolfCandidate.OuterForestSuffix
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestHalt
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def Post : Option (HashOutput×SharedForest.Witness×List Nat) → MachineState → Prop
  | none,s=>OuterFinalPost.Post [] none s
  | some (output,w,ns),s=>OuterFinalPost.Post ns (some (output,w)) s

theorem suffix {sk : BitVec 256} (ns : List Nat) (r : Option (HashOutput×SharedForest.Witness)) (s : MachineState)
    (h : OuterLayersRecovery.SuffixDone ns r s) :
    TBSim OuterImages.expandImage sk s OuterSuffix.work (pure (OuterForestSuffix.appendNonces ns r)) Post := by
  have H:=OuterSuffix.suffix_done (sk:=sk) ns h
  have H' : TBSim OuterImages.expandImage sk s OuterSuffix.work (pure r)
      (fun result t=>Post (OuterForestSuffix.appendNonces ns result) t) := H.mono le_rfl (by
    intro result t hr
    cases result with
    | none=>exact hr
    | some p=>rcases p with ⟨out,w⟩;exact hr)
  have HM:=OuterNodeSourceSim.map_sim (OuterForestSuffix.appendNonces ns) H'
  simpa only [map_pure] using HM

theorem finish {sk : BitVec 256} {r : Option (HashOutput×SharedForest.Witness×List Nat)} {s : MachineState}
    (h : OuterForestSuffix.SuffixDone r s) :
    TBSim OuterImages.expandImage sk s OuterSuffix.work (pure r) Post := by
  cases r with
  | none=>exact suffix [] none s h
  | some p=>rcases p with ⟨out,w,ns⟩;exact suffix ns (some (out,w)) s h

#print axioms finish
end OuterForestHalt
