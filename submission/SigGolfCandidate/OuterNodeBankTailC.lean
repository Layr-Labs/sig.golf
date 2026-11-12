import SigGolfCandidate.OuterNodeBankStepsC
import SigGolfCandidate.OuterNodeHandFinishC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterNodeBankTailC
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Verify W9Machine W9Drv.SharedCProof
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

def program (coord index j l n : Nat) (pads sibs tws : Nat→Digest) (v : Digest) : M (Nat×Digest) := do
  let v5←(List.range' l n).foldlM (childLevelP coord index j pads (hpOf j tws) sibs) v
  OuterGroundCore.nodeAt coord index (heapOf 5 j)
    (if bitAt j 5=0 then v5 else sibs 5) (if bitAt j 5=0 then sibs 5 else v5)

theorem run {im : Image} {sk : BitVec 256} (j : Fin 128) (coord : Fin 9) (index : Nat)
    (hc1 : 1≤coord.val) (hc8 : coord.val=8) (hi : index<2^31)
    (hc : CodeAt im (pcOf (childBase j.val)) (OuterNodeBankLayout.cWords j.val))
    {leaf pads sibs tws : Nat→Digest} {u s : MachineState}
    (hu : ChildPre j.val (coordRegion coord.val) coord.val index leaf pads sibs tws u)
    (n l : Nat) (v : Digest) (hln : l+n=5)
    (hs : Mid j.val (coordRegion coord.val) coord.val index u l v s) :
    TBSim im sk s (cycR j.val l n+77844) (program coord.val index j.val l n pads sibs tws v)
      (OuterNodeHandFinishC.Post coord.val j.val u) := by
  unfold program
  exact TBSim.bind (OuterNodeBankStepsC.rest_tbsim (sk:=sk) j.isLt hc hu n l v s hln hs)
    (fun v5 s5 hmid=>OuterNodeHandFinishC.run j coord index hc1 hc8 hi hc hu v5 hmid)

#print axioms run
end OuterNodeBankTailC
