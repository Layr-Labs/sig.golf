import SigGolfCandidate.OuterSharedCPost
import SigGolfCandidate.OuterChildModelC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSharedCRun
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open W9Machine W9Drv.SharedCProof SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

theorem run {L : W9Machine.Layout} {sk : BitVec 256} (k : Fin 9) (raw : Fin 128) (index : Nat)
    (hf : SharedV3.first k.val=false) (hc : k.val=8) (hi : index<2^31)
    (hchild : L.childWord raw=copyBase (SharedV3.physical k.val raw.val))
    (hcode : CopyCodeAt L.image (SharedV3.physical k.val raw.val))
    (hbank : CodeAt L.image (pcOf (childBase (SharedV3.physical k.val raw.val))) (OuterNodeBankLayout.cWords (SharedV3.physical k.val raw.val)))
    (hS : CodeAt L.image (pcOf SEARCH) searchWords)
    (hT : CodeAt L.image (pcOf (trampOf (SharedV3.physical k.val raw.val)))
      (trampWords (trampOf (SharedV3.physical k.val raw.val)) SEARCH (siteB (SharedV3.physical k.val raw.val)+1)))
    (hS16 : CodeAt L.image (pcOf SEARCH16) search16Words)
    (hT16 : CodeAt L.image (pcOf (tramp16Of (SharedV3.physical k.val raw.val)))
      (trampWords (tramp16Of (SharedV3.physical k.val raw.val)) SEARCH16 (site16C (SharedV3.physical k.val raw.val)+1)))
    (hbase : Chain.base L k=coordRegion k.val)
    (w : ClaudeWCT.W9.T3M.WBytes) (ends : List Digest) (x : MachineState)
    (hx : SharedChild.Pre L w index k raw ends x) :
    TBSim L.image sk x (OuterCopyChildC.W k.val (SharedV3.physical k.val raw.val)+0)
      (OuterChildModel.childProgram w index k raw ends) (OuterSharedPost.Post L k raw x) := by
  have hpj:=SharedV3.physical_lt k.val raw.val raw.isLt
  let j : Fin 128:=⟨_,hpj⟩
  have hc1 : 1≤k.val := by
    by_contra h
    have hz : k.val=0 := by omega
    simp [SharedV3.first,hz] at hf
  have hp:=pre_of_shared w index k raw ends x (bankPc j.val x) hx (fun _=>rfl) (fun _=>rfl) rfl
  have hp' : ChildPre j.val (coordRegion k.val) k.val index
      (V3.leafFields k.val index raw.val (SharedV3.leafPad w k.val) ends)
      (SharedV3.nodePad w k.val j.val) (SharedV3.sibling w k.val j.val) (SharedV3.nodeTw w k.val j.val) (bankPc j.val x) := by
    simpa only [hbase] using hp
  have H:=OuterCopyChildC.run (sk:=sk) j k index hc1 hc hi hcode hbank hS hT hS16 hT16 hp' rfl (by rw [hx.pc,hchild])
  rw [OuterChildModelC.program_eq w index k raw ends hf hc]
  exact TBSim.bind H (fun r t ht=>TBSim.pure (a:=(r.2.2.2,r.1,r.2.1,r.2.2.1))
    (OuterSharedCPost.post_of w index k raw ends x hf hc hx hbase r t
      (OuterCopyChildFlatC.flatten k j index (bankPc j.val x) t r ht)))

#print axioms run
end OuterSharedCRun
