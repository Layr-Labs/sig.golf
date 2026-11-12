import SigGolfCandidate.OuterSignCall
import SigGolfCandidate.OuterSignFallbackCall
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignPlainCase
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash)
open SigGolfCandidate.FtsGrind
open SphincsSecurity (bytesLE)

theorem canonical {sk : BitVec 256} {tb ret heap A D coord index : Nat} {left right : Digest} {s u : MachineState}
    (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
    (F : SignIn tb ret heap A D (OuterNodeRawModel.pre coord index heap left) (bytesLE 16 (0:Digest)) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hD : 2048≤D) (hDi : D<2^20) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3)
    (hng : ¬(8≤heap ∧ heap<16)) (hp : u.pc=pcOf 25338)
    (hr : RegsExcept s u [.x16,.x17]) (h16 : u.getReg .x16=pcOf (tb+2))
    (sv0 : u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14) (sv1 : u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17)
    (sv4 : u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16)
    (hf : Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)) :
    TBSim OuterImages.signImage sk u 77865 (OuterNodeRawModel.raw coord index heap left right (OuterGroundCore.cap coord-1) 0)
      (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
  have ha : 2048≤A := by omega
  have hai : A<2^20 := by omega
  have FI:=OuterSignInput.search F hr hf ha hai hD hDi
  have hmid:=F.mmid
  rw [wordsOf_bytesLE16,readWords_two] at hmid
  have hz : s.getMem (BitVec.ofNat 64 (A+32))=0 ∧ s.getMem (BitVec.ofNat 64 (A+40))=0 := by
    simpa [show A+32+8=A+40 by omega] using hmid
  have z32 : u.getMem (BitVec.ofNat 64 (A+32))=0 := (hf.get (by omega) (by omega)).trans hz.1
  have z40 : u.getMem (BitVec.ofNat 64 (A+40))=0 := (hf.get (by omega) (by omega)).trans hz.2
  have H:=OuterSignCall.raw (sk:=sk) FI hA hc hc9 hi hh hp z32 z40
  have H':=TBSim.bind (W₂:=9) H (fun r t ht=>OuterSignPlainFinish.finish hT F hD hng ht hr h16 sv0 sv1 sv4 hf)
  simpa using H'

theorem fallback {sk : BitVec 256} {tb ret heap A D : Nat} {pre mid right : List UInt8} {s u : MachineState}
    (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
    (F : SignIn tb ret heap A D pre mid right s) (hA : 2048≤A) (hAi : A<2^20) (hD : 2048≤D) (hDi : D<2^20)
    (hbad : OuterSignFallback.Bad A u) (hng : ¬(8≤heap ∧ heap<16)) (hp : u.pc=pcOf 25338)
    (hr : RegsExcept s u [.x16,.x17]) (h16 : u.getReg .x16=pcOf (tb+2))
    (sv0 : u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14) (sv1 : u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17)
    (sv4 : u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16)
    (hf : Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)) :
    TBSim OuterImages.signImage sk u 35 ((fun a=>(0,a)) <$> publicHash (pre++mid++right))
      (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
  have FI:=OuterSignInput.plain F hr hf hA hAi hD hDi
  have H:=OuterSignFallbackCall.run (sk:=sk) FI hbad hp
  have H':=TBSim.bind (W₂:=9) H (fun a t ht=>OuterSignPlainFinish.finish (r:=(0,a)) hT F hD hng ht hr h16 sv0 sv1 sv4 hf)
  rw [map_eq_bind_pure_comp]
  change TBSim OuterImages.signImage sk u 35 (publicHash (pre++mid++right) >>= fun a=>pure (0,a)) (OuterSignInterface.Out s ret heap D (2-signR tb))
  exact H'
#print axioms canonical
#print axioms fallback
end OuterSignPlainCase
