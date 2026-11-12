import SigGolfCandidate.OuterSignInput
import SigGolfCandidate.OuterSignFallback
import SigGolfCandidate.OuterControlRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignFallbackCall
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash)
open SigGolfCandidate.FtsGrind

theorem run {sk : BitVec 256} {A D : Nat} {input : List UInt8} {s : MachineState}
    (F : OuterSignPlain.Input A D input s) (hb : OuterSignFallback.Bad A s) (hp : s.pc=pcOf 25338) :
    TBSim OuterImages.signImage sk s 26 (publicHash input) (OuterSignPlain.Out s D) := by
  obtain ⟨u,su,up,ur,um⟩:=OuterControlRun.jump 25338 26156 (by decide) (by decide) OuterImageSignWindows.sign_jump s hp
  have fu : Frame s u (fun _=>False) := by intro X hX hn;exact um _
  have F' : OuterSignPlain.Input A D input u :=
    { x5:=by rw [ur];exact F.x5
      x10:=by rw [ur];exact F.x10
      x11:=by rw [ur];exact F.x11
      x12:=by rw [ur];exact F.x12
      len:=F.len
      words:=by rw [frame_readWordsG fu A 8 (by have:=F.ahi;omega) (by intro i hi h;exact h)];exact F.words
      alo:=F.alo
      ahi:=F.ahi
      aa:=F.aa
      dlo:=F.dlo
      dhi:=F.dhi
      da:=F.da }
  have hb' : OuterSignFallback.Bad A u := by simpa only [OuterSignFallback.Bad,um] using hb
  have H:=OuterSignFallback.run (sk:=sk) F' hb' OuterImageHelpers.sign_helper up
  refine TBSim.steps su (H.mono le_rfl ?_)
  intro r t ht
  refine ⟨ht.at_pc,?_,ht.output,?_⟩
  · intro x hx
    rw [ht.regs.get hx,ur]
  · exact (fu.trans ht.frame).mono (by intro X hX h;rcases h with h|h;exact h.elim;exact h)
#print axioms run
end OuterSignFallbackCall
