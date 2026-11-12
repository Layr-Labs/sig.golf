import SigGolfCandidate.OuterSharedBank
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterChildView
open OracleComp SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.T3M
open W9Machine W9Machine.SharedV3 W9Machine.V3
open SigGolfCandidate.T3 (Digest M)

theorem view (B : Nat) (w : SharedV3.WBytes) (index : Nat) (k : Fin 9) (u : MachineState)
    (raw : Fin 128) (ends : List Digest) (padL padR : Digest)
    (hL : DigAt u (B+regionOffset k.val+672) padL)
    (hR : DigAt u (B+regionOffset k.val+160) padR) :
    OuterChildModel.childProgram (viewWB B w k.val u) index k raw ends=
      OuterChildModel.child w index k raw ends padL padR := by
  have hn : k.val≤8 := by omega
  let j : Fin 128 := ⟨physical k.val raw.val,physical_lt _ _ raw.isLt⟩
  unfold OuterChildModel.childProgram
  rw [leafPad_viewB B w k.val u hn padL hL,nodePad4_viewB B w k.val u hn j padR hR]
  unfold OuterChildModel.child
  cases hf : first k.val with
  | true=>
    simp only [hf,if_true]
    have H:=childNG_viewB B w index k u raw ends padL padR hL hR
    unfold SharedChild.childProgramG at H
    rw [leafPad_viewB B w k.val u hn padL hL,nodePad4_viewB B w k.val u hn j padR hR] at H
    rw [H]
  | false=>
    have hi (l : Nat) (hl : l<6) (value : Digest) :
        childInput (viewWB B w k.val u) index k.val (physical k.val raw.val) padR value l=
          childInput w index k.val (physical k.val raw.val) padR value l :=
      childInput_viewB B w index k.val u hn j padR value l hl
    have hs (l : Nat) (hl : l<6) : SharedV3.sibling (viewWB B w k.val u) k.val (physical k.val raw.val) l=
        SharedV3.sibling w k.val (physical k.val raw.val) l := sibling_viewB B w k.val u hn j l hl
    have hh (l : Nat) : SharedV3.nodeHPad (viewWB B w k.val u) k.val (physical k.val raw.val) l=
        SharedV3.nodeHPad w k.val (physical k.val raw.val) l := nodeHPad_viewB B w k.val u hn j l
    simp only [hf,Bool.false_eq_true,if_false,show List.range 5=[0,1,2,3,4] from rfl,
      List.foldlM_cons,List.foldlM_nil,childStepG,hi 0 (by decide),hi 1 (by decide),
      hi 2 (by decide),hi 3 (by decide),hi 4 (by decide),hs 2 (by decide),hs 3 (by decide),hs 5 (by decide),hh]

#print axioms view
end OuterChildView
