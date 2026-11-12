import SigGolfCandidate.OuterSignNodeModel
import SigGolfCandidate.OuterSignTrampCode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignTrampRun
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash)
open SigGolfCandidate.FtsGrind ClaudeWCT.W9.Machine.Sign
open SphincsSecurity (bytesLE)

theorem run {sk : BitVec 256} {c index heap : Nat} {L pad R : Digest} {s : MachineState}
    (hc : c<9) (hi : index<2^31) (hh : 2≤heap) (hh128 : heap<128)
    (houter : heap<4→1≤c ∧ pad=0)
    (F : SignIn (SIGN_TRAMP+5*c) (SharedNode.hashPc c+1) heap NODEW NOUTW
      (ftsPre c index heap L) (bytesLE 16 pad) (bytesLE 16 R) s) :
    TBSim OuterImages.signImage sk s (signW (ftsWidth c) heap (decide (c<4))+77865)
      (OuterSignInterface.program (ftsWidth c) heap (decide (c<4)) (ftsPre c index heap L) (bytesLE 16 R)
        (OuterSignNodeModel.plain c index heap pad L R))
      (OuterSignInterface.Out s (SharedNode.hashPc c+1) heap NOUTW (ftsWidth c)) := by
  have ht:=OuterSignTrampCode.tramp c hc
  have h16:=OuterSignTrampCode.s16
  by_cases ho : heap=2 ∨ heap=3
  · have hlt : heap<4 := by rcases ho with rfl|rfl <;> omega
    obtain ⟨hc1,hpad⟩:=houter hlt
    subst pad
    have hn : ¬(8≤heap ∧ heap<16) := by omega
    have hn16 : ¬G16 (decide (c<4)) heap := by unfold G16;omega
    simp only [OuterSignInterface.program,OuterSignNodeModel.plain,if_neg hn,if_neg hn16,if_pos ho,signW]
    have H:=OuterSignRoundTrip.outer_node (sk:=sk) ht h16 F (by rfl) (by decide) (by decide) hc1 hc hi ho
    rw [signR_width c hc] at H
    exact H
  · have hh4 : 4≤heap := by omega
    have H:=OuterSignRoundTrip.other_node (sk:=sk) ht h16 F (by decide) (by decide) (by decide) (by decide) hc hh4 hh128
    rw [signR_width c hc,signSel_coord c hc] at H
    simp only [OuterSignNodeModel.plain,if_neg ho]
    change TBSim OuterImages.signImage sk s (signW (ftsWidth c) heap (decide (c<4))+77865)
      (signNode (ftsWidth c) heap (decide (c<4)) (ftsPre c index heap L) (bytesLE 16 pad) (bytesLE 16 R))
      (OuterSignInterface.Out s (SharedNode.hashPc c+1) heap NOUTW (ftsWidth c))
    exact H.mono (by omega) (fun _ _ h=>h)
#print axioms run
end OuterSignTrampRun
