import SigGolfCandidate.OuterNodeBankSetup
import SigGolfCandidate.OuterNodeBankSetupC
import SigGolfCandidate.OuterNodeControllerGeometry
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeBufferInput
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3 ClaudeWCT.WCT9
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant
open SphincsSecurity (bytesLE bytesLE_length)

theorem of_points (A D coord index heap : Nat) (left right : Digest) (s : MachineState)
    (h5 : s.getReg .x5=0) (h10 : s.getReg .x10=BitVec.ofNat 64 A)
    (h11 : s.getReg .x11=64) (h12 : s.getReg .x12=BitVec.ofNat 64 D)
    (hleft : DigAt s A left) (hheader : DigAt s (A+16) (wctNodeHeader coord index heap))
    (hright : DigAt s (A+48) right)
    (hgeom : 2048≤A ∧ A<2^20 ∧ A%8=0 ∧ 2048≤D ∧ D<2^20 ∧ D%8=0 ∧ D+32≤A) :
    Input A D (OuterNodeRawModel.pre coord index heap left) (OuterNodeRawModel.rightBytes right) s := by
  refine ⟨h5,h10,h11,h12,?_,?_,?_,?_,hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2.1,
    hgeom.2.2.2.2.1,hgeom.2.2.2.2.2.1,Or.inl hgeom.2.2.2.2.2.2⟩
  · simp only [OuterNodeRawModel.pre,List.length_append,bytesLE_length]
  · exact bytesLE_length _ _
  · unfold OuterNodeRawModel.pre
    rw [wordsOf_append _ _ (by simp [bytesLE_length]),wordsOf_bytesLE16,wordsOf_bytesLE16]
    rw [show 4=2+2 from rfl,readWords_add,readWords_two,readWords_two]
    simp only [hleft.1,hleft.2,show A+8*2=A+16 by omega,hheader.1,hheader.2]
  · unfold OuterNodeRawModel.rightBytes
    rw [wordsOf_bytesLE16,readWords_two,hright.1,hright.2]

theorem header (coord : Fin 9) (index heap : Nat) :
    W9Machine.V3.nodeHdr coord.val index heap 0=wctNodeHeader coord.val index heap := by
  rw [W9Drv.nodeHdr_canonical,SigGolfCandidate.T3M.SecurityInputs.withHigh_nodeTweak_zero]
  rfl

#print axioms header

#print axioms of_points
end OuterNodeBufferInput
