import SigGolfCandidate.OuterSignRoundTrip
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignNodeModel
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash)
open SigGolfCandidate.FtsGrind ClaudeWCT.W9.Machine.Sign
open SphincsSecurity (bytesLE)

def plain (c index heap : Nat) (pad L R : Digest) : M (Nat×HashOutput) :=
  if heap=2 ∨ heap=3 then OuterNodeRawModel.raw c index heap L R (OuterGroundCore.cap c-1) 0
  else (fun a=>(0,a)) <$> publicHash (ftsPre c index heap L++bytesLE 16 pad++bytesLE 16 R)

def hashProgram (c index heap : Nat) (pad L R : Digest) : M Digest :=
  if heap=2 ∨ heap=3 then Prod.snd <$> OuterGroundCore.nodeAt c index heap L R
  else SharedNode.hashProgram c index heap pad L R

theorem high_eq (c heap : Nat) (hc : c<9) (hh : heap=2 ∨ heap=3) :
    SharedNode.high c heap=OuterNodeRawModel.high c heap := by
  rcases hh with rfl|rfl <;> interval_cases c <;> decide

theorem kept (c index heap : Nat) (L R : Digest) (hc : c<9) (hh : heap=2 ∨ heap=3) :
    (Prod.snd <$> OuterGroundCore.nodeAt c index heap L R)=
      (OuterNodeRawModel.raw c index heap L R (OuterGroundCore.cap c-1) 0 >>= fun r=>pure (SharedNode.half (SharedNode.high c heap) r.2)) := by
  rw [high_eq c heap hc hh]
  have he : ∀ a,SharedNode.half (OuterNodeRawModel.high c heap) a=OuterGroundCore.value c heap a := by
    intro a
    simpa only [SharedNode.half,SigGolfCandidate.FtsGrind.halfOf] using OuterNodeRawModel.half_value c heap a
  simp only [he]
  rw [OuterGroundCore.nodeAt,OuterNodeRawModel.source_eq,Functor.map_map,map_eq_bind_pure_comp]
  rfl

theorem trampoline (c index heap : Nat) (pad L R : Digest) (hc : c<9) :
    hashProgram c index heap pad L R=
      (OuterSignInterface.program (ftsWidth c) heap (decide (c<4)) (ftsPre c index heap L) (bytesLE 16 R) (plain c index heap pad L R) >>=
        fun r=>pure (SharedNode.half (SharedNode.high c heap) r.2)) := by
  by_cases hh : heap=2 ∨ heap=3
  · have hn : ¬(8≤heap ∧ heap<16) := by rcases hh with rfl|rfl <;> omega
    have hn16 : ¬G16 (decide (c<4)) heap := by unfold G16;rcases hh with rfl|rfl <;> omega
    simp only [hashProgram,if_pos hh,OuterSignInterface.program,if_neg hn,if_neg hn16,plain]
    exact kept c index heap L R hc hh
  · rw [hashProgram,if_neg hh,SharedNode.hashProgram_tramp]
    simp only [OuterSignInterface.program,plain,if_neg hh,signNode]
#print axioms high_eq
#print axioms kept
#print axioms trampoline
end OuterSignNodeModel
