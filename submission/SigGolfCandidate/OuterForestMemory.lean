import SigGolfCandidate.OuterInstalledForest
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestMemory
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT.W9.T3M
open SigGolfCandidate.T3M.Search (ENC NODE TOP_DATA NBUF OutAt)
open SigGolfCandidate.T3M.Expand (CHAIN)
open ClaudeWCT.W9.Machine.Expand.SharedCompactMain
macro "outer_frame_omega" : tactic => `(tactic| (simp only [OuterForestFrame.writes,ClaudeWCT.W9.Machine.Expand.SharedForestRun.writes,W9Machine.SharedChild.scratchW,SigGolfCandidate.FtsGrind.SCR,SigGolfCandidate.FtsGrind.SCR16] at *;omega))

theorem memory_frame {output : HashOutput} {b : SharedCodec.CBytes} {counter : BitVec 32} {pk : Digest}
    {s t : MachineState} (h : ForestMemory output b counter pk s)
    (hf : Frame s t OuterForestFrame.writes) :
    ForestMemory output b counter pk t := by
  have mem (A:Nat) (ha:A<2^64) (hn:¬OuterForestFrame.writes A) :=
    hf.get ha hn
  constructor
  · exact h.stable.frame hf (by intro A hk;unfold Keep at hk;outer_frame_omega)
  · exact h.inflated.frame hf (by intro A ha hb;outer_frame_omega)
  · exact h.hintsLt
  · change t.getMem (BitVec.ofNat 64 0x66000)=_
    rw [mem _ (by outer_frame_omega) (by outer_frame_omega)]
    exact h.hints
  · change t.getMem (BitVec.ofNat 64 0x66008)=_
    rw [mem _ (by outer_frame_omega) (by outer_frame_omega)]
    exact h.dc
  · obtain ⟨x,hx,hm⟩:=h.c32
    exact ⟨x,hx,(mem _ (by unfold ENC;outer_frame_omega) (by unfold ENC;outer_frame_omega)).trans hm⟩
  · exact ⟨(mem _ (by unfold CHAIN;outer_frame_omega) (by unfold CHAIN;outer_frame_omega)).trans h.zero.c0,
      (mem _ (by unfold CHAIN;outer_frame_omega) (by unfold CHAIN;outer_frame_omega)).trans h.zero.c8,
      (mem _ (by unfold NODE;outer_frame_omega) (by unfold NODE;outer_frame_omega)).trans h.zero.n32,
      (mem _ (by unfold NODE;outer_frame_omega) (by unfold NODE;outer_frame_omega)).trans h.zero.n40,
      (mem _ (by unfold ENC;outer_frame_omega) (by unfold ENC;outer_frame_omega)).trans h.zero.e40⟩
  · exact h.table.frame hf (by intro i hi;unfold TOP_DATA;outer_frame_omega)
  · exact h.cf.frame hf (by intro i hi hj;unfold TOP_DATA;outer_frame_omega)
  · exact h.reward.frame hf (by intro i hi hj;unfold TOP_DATA;outer_frame_omega)
  · intro A ha hb;rw [mem _ (by outer_frame_omega) (by outer_frame_omega)];exact h.regionZero A ha hb
  · exact h.proj


#print axioms memory_frame
end OuterForestMemory
