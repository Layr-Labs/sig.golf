import SigGolfCandidate.OuterChildView
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterSharedCore
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
open SigGolfCandidate.Rv SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify W9Machine
open SigGolfCandidate.T3 (Digest M)

def Post (L : W9Machine.Layout) (w : W9Machine.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128)
    (entry : MachineState) (res : Digest×Nat×Nat×Nat) (result : MachineState) : Prop :=
  ∃ ends childEntry,Chain.Post L w index k raw entry ends childEntry ∧
    OuterSharedPost.Post L k raw childEntry res result

theorem run (L : W9Machine.Layout) (sk : BitVec 256) (codes : OuterSharedBank.Codes L.image)
    (k : Fin 9) (raw : Fin 128) (rank : Fin 563)
    (hchild : L.childWord raw=W9Drv.SharedBank.copyWord k.val raw.val)
    (hbase : Chain.base L k=9768-848*k.val)
    (hchain : ∀ w index u,N600.Pre L w index k raw rank u →
      TBSim L.image sk u 89 (N600.program w index k raw rank) (N600.Post L w index k raw u))
    (w : W9Machine.WBytes) (index : Nat) (hi : index<2^31) (snapshot u : MachineState) (padL padR : Digest)
    (hu : N600.Pre L (SharedV3.viewWB 2904 w k.val snapshot) index k raw rank u)
    (hL : DigAt snapshot (2904+V3.regionOffset k.val+672) padL)
    (hR : DigAt snapshot (2904+V3.regionOffset k.val+160) padR) :
    TBSim L.image sk u (89+OuterSharedBank.cost k)
      (N600.program w index k raw rank >>=fun ends=>OuterChildModel.child w index k raw ends padL padR)
      (Post L (SharedV3.viewWB 2904 w k.val snapshot) index k raw u) := by
  have hspec : (N600.program w index k raw rank >>=fun ends=>OuterChildModel.child w index k raw ends padL padR)=
      (N600.program (SharedV3.viewWB 2904 w k.val snapshot) index k raw rank >>=fun ends=>
        OuterChildModel.childProgram (SharedV3.viewWB 2904 w k.val snapshot) index k raw ends) := by
    unfold N600.program
    rw [SharedV3.chainProgram_viewB]
    simp only [fun ends=>OuterChildView.view 2904 w index k snapshot raw ends padL padR hL hR]
  rw [hspec]
  refine TBSim.bind (hchain _ _ _ hu) ?_
  intro ends childEntry hp
  have hb : Chain.base L k=ClaudeWCT.W9.Machine.Expand.SharedScatter.coordRegion k.val := by
    rw [hbase,OuterNodeControllerGeometry.actual_frame k]
    unfold OuterNodeBufferGeometry.frameBase V3.regionOffset
    have :=k.isLt
    omega
  exact (OuterSharedBank.run L sk k raw codes hchild hb _ index hi ends childEntry (hp.sharedChild hu)).mono
    le_rfl (fun res t ht=>⟨ends,childEntry,hp,ht⟩)

#print axioms run
end OuterSharedCore
