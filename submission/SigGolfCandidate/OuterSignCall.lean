import SigGolfCandidate.OuterSignInput
import SigGolfCandidate.OuterControlRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignCall
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M)
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant

theorem raw {sk : BitVec 256} {A D coord index heap : Nat} {left right : Digest} {s : MachineState}
    (F : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3)
    (hp : s.pc=pcOf 25338) (hz32 : s.getMem (BitVec.ofNat 64 (A+32))=0)
    (hz40 : s.getMem (BitVec.ofNat 64 (A+40))=0) :
    TBSim OuterImages.signImage sk s 77856 (OuterNodeRawModel.raw coord index heap left right (OuterGroundCore.cap coord-1) 0)
      (fun r t=>OuterSignPlain.Out s D r.2 t) := by
  obtain ⟨u,su,up,ur,um⟩:=OuterControlRun.jump 25338 26156 (by decide) (by decide) OuterImageSignWindows.sign_jump s hp
  have fu : Frame s u (fun _=>False) := by intro X hX hn;exact um _
  have F' : Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) u :=
    { x5:=by rw [ur];exact F.x5
      x10:=by rw [ur];exact F.x10
      x11:=by rw [ur];exact F.x11
      x12:=by rw [ur];exact F.x12
      pre_len:=F.pre_len
      right_len:=F.right_len
      pre_words:=by rw [frame_readWordsG fu A 4 (by have:=F.ahi;omega) (by intro i hi h;exact h)];exact F.pre_words
      right_words:=by rw [frame_readWordsG fu (A+48) 2 (by have:=F.ahi;omega) (by intro i hi h;exact h)];exact F.right_words
      alo:=F.alo
      ahi:=F.ahi
      aa:=F.aa
      dlo:=F.dlo
      dhi:=F.dhi
      da:=F.da
      disjoint:=F.disjoint }
  have H:=OuterSignCanonical.run_raw (sk:=sk) F' hA hc hc9 hi hh OuterImageHelpers.sign_helper up
  refine TBSim.steps su (H.mono le_rfl ?_)
  intro r t ht
  have hc':=OuterSignPlainFinish.canonical_call ht (by rw [um];exact hz32) (by rw [um];exact hz40)
  refine ⟨hc'.at_pc,?_,hc'.output,?_⟩
  · intro x hx
    rw [hc'.regs.get hx,ur]
  · exact (fu.trans hc'.frame).mono (by intro X hX h;rcases h with h|h;exact h.elim;exact h)
#print axioms raw
end OuterSignCall
