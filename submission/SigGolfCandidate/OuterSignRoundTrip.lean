import SigGolfCandidate.OuterSignPlainCase
import SigGolfCandidate.OuterSignHeader
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSignRoundTrip
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest HashOutput M publicHash)
open SigGolfCandidate.FtsGrind
open SphincsSecurity (bytesLE)

theorem outer_node {sk : BitVec 256} {tb ret heap A D coord index : Nat} {left right : Digest} {s : MachineState}
    (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
    (hS16 : CodeAt OuterImages.signImage (pcOf SIGN_S16) signS16Words)
    (F : SignIn tb ret heap A D (OuterNodeRawModel.pre coord index heap left) (bytesLE 16 (0:Digest)) (OuterNodeRawModel.rightBytes right) s)
    (hA : A=328448) (hD : 2048≤D) (hDi : D<2^20) (hc : 1≤coord) (hc9 : coord<9) (hi : index<2^31) (hh : heap=2 ∨ heap=3) :
    TBSim OuterImages.signImage sk s 77897 (OuterNodeRawModel.raw coord index heap left right (OuterGroundCore.cap coord-1) 0)
      (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
  let P:=OuterNodeRawModel.raw coord index heap left right (OuterGroundCore.cap coord-1) 0
  have hp : ∀ u,¬(8≤heap ∧ heap<16)→u.pc=pcOf 25338→
      RegsExcept s u [.x16,.x17]→u.getReg .x16=pcOf (tb+2)→
      u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14→u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17→
      u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16→Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)→
      TBSim OuterImages.signImage sk u 77865 P (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
    intro u hn hup hr h16 sv0 sv1 sv4 hf
    exact OuterSignPlainCase.canonical hT F hA hD hDi hc hc9 hi hh hn hup hr h16 sv0 sv1 sv4 hf
  have H:=OuterSignTrip.sign_tramp_node hT hS16 F P 77865 hp
  have hn : ¬(8≤heap ∧ heap<16) := by rcases hh with rfl|rfl <;> omega
  have hn16 : ¬G16 (signSel tb) heap := by unfold G16;rcases hh with rfl|rfl <;> omega
  simpa only [OuterSignInterface.program,signW,if_neg hn,if_neg hn16] using H

theorem other_node {sk : BitVec 256} {tb ret heap A D coord index : Nat} {left pad right : Digest} {s : MachineState}
    (hT : CodeAt OuterImages.signImage (pcOf tb) (trampWords tb SIGN_S16 ret))
    (hS16 : CodeAt OuterImages.signImage (pcOf SIGN_S16) signS16Words)
    (F : SignIn tb ret heap A D (OuterNodeRawModel.pre coord index heap left) (bytesLE 16 pad) (OuterNodeRawModel.rightBytes right) s)
    (hA : 2048≤A) (hAi : A<2^20) (hD : 2048≤D) (hDi : D<2^20) (hc : coord<9) (hh4 : 4≤heap) (hh128 : heap<128) :
    TBSim OuterImages.signImage sk s (signW (2-signR tb) heap (signSel tb)+35)
      (signNode (2-signR tb) heap (signSel tb) (OuterNodeRawModel.pre coord index heap left) (bytesLE 16 pad) (OuterNodeRawModel.rightBytes right))
      (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
  let P:=((fun a=>(0,a)) <$> publicHash (OuterNodeRawModel.pre coord index heap left++bytesLE 16 pad++OuterNodeRawModel.rightBytes right))
  have hp : ∀ u,¬(8≤heap ∧ heap<16)→u.pc=pcOf 25338→
      RegsExcept s u [.x16,.x17]→u.getReg .x16=pcOf (tb+2)→
      u.getMem (BitVec.ofNat 64 1104)=s.getReg .x14→u.getMem (BitVec.ofNat 64 1112)=s.getReg .x17→
      u.getMem (BitVec.ofNat 64 1136)=s.getReg .x16→Frame s u (fun X=>X=1104 ∨ X=1112 ∨ X=1136)→
      TBSim OuterImages.signImage sk u 35 P (OuterSignInterface.Out s ret heap D (2-signR tb)) := by
    intro u hn hup hr h16 sv0 sv1 sv4 hf
    have FI:=OuterSignInput.search F hr hf hA hAi hD hDi
    exact OuterSignPlainCase.fallback hT F hA hAi hD hDi (OuterSignHeader.fallback FI hc hh4 hh128) hn hup hr h16 sv0 sv1 sv4 hf
  have H:=OuterSignTrip.sign_tramp_node hT hS16 F P 35 hp
  exact H
#print axioms outer_node
#print axioms other_node
end OuterSignRoundTrip
