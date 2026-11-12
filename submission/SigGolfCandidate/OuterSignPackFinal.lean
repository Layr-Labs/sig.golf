import SigGolfCandidate.OuterLooseInput
import SigGolfCandidate.OuterControlRun
import SigGolfCandidate.OuterImageSignWindows
import SigGolfCandidate.Merge096
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignPackFinal
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterSignatureCodec

theorem run (sig : OldSig) (s : MachineState) (hp : s.pc=pcOf 25963)
    (h5 : s.getReg .x5=1) (h10 : s.getReg .x10=0)
    (hw : ∀i,i<648→s.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64)
    (ht : (s.getMem 33856).extractLsb' 0 16=sig.extractLsb' (8*5184) 16) :
    ∃t,Steps OuterImages.signImage s 34 34 t ∧ t.pc=pcOf 26240 ∧
      t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t 28672 5184=OuterLooseCodec.compress sig ∧
      fetch OuterImages.signImage t=some (.base .ECALL) := by
  obtain ⟨u,su,up,ur,um⟩:=OuterControlRun.jump 25963 26207 (by decide) (by decide)
    OuterImageSignWindows.pack_jump s hp
  let t:=packBlock.res.toState u
  have ut : Steps OuterImages.signImage u 33 33 t:=
    symRun_sound packBlock OuterImageHelpers.sign_pack u up (pack_obligs u)
  have tp : t.pc=pcOf 26240:=rfl
  have uw : ∀i,i<648→u.getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64:=by
    intro i hi
    rw [um]
    exact hw i hi
  have uh : (u.getMem 33856).extractLsb' 0 16=(splitOld sig).2:=by rw [um];exact ht
  have tw:=OuterLooseInput.words sig u uw uh
  refine ⟨t,su.trans ut,tp,?_,?_,?_,OuterImageControlTransfers.sign_halt.fetch t tp⟩
  · change u.getReg .x5=1
    rw [ur,h5]
  · change u.getReg .x10=0
    rw [ur,h10]
  · exact ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput.readBuffer_words t 28672 5184 648
      (OuterLooseCodec.compress sig) (by decide) (by decide) (by decide) tw
#print axioms run
end OuterSignPackFinal
