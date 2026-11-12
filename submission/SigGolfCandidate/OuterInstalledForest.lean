import SigGolfCandidate.OuterForestRun
import SigGolfCandidate.OuterImageCopies
import SigGolfCandidate.OuterInstalledChain
import SigGolfCandidate.OuterInstalledDispatch
import SigGolfCandidate.OuterWitnessForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInstalledForest
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine
open ClaudeWCT.W9.Machine.Expand

theorem run (sk : BitVec 256) (w : W9Machine.WBytes) (index : Nat) (hi : index<2^31)
    (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563) (initial : MachineState)
    (h0 : OuterForestInv.Inv w index raw ranks initial 0 (SharedV3.initialPair w) initial) :
    TBSim OuterImages.expandImage sk initial OuterForestRun.forestW (OuterForestModel.forest w index raw ranks)
      (OuterForestRun.ForestPost initial index raw ranks) := by
  apply OuterForestRun.forest_tbsim OuterImages.expandImage sk w index raw ranks initial ?_ h0
  intro k prev u hu
  apply OuterForestStep.step_tbsim OuterImages.expandImage sk SharedDispatch.checked OuterInstalledDispatch.code W9Drv.slot_entry ?_
    w index hi raw ranks initial k prev u hu
  intro L k j rank himage hc hb hcw w index hi snapshot u padL padR hpre hL hR
  have codes : OuterSharedBank.Codes L.image := by
    rw [himage]
    exact OuterImageCopies.codes
  have hw : (Frozen.image.code.drop 195584).take 36032=(L.image.code.drop 195584).take 36032 := by
    rw [himage]
    exact OuterInstalledChain.window
  exact OuterSharedCore.run L sk codes k j rank hc hb
    (fun w index u hu=>OuterChainBank.run L sk hw hcw rank w index k j u hu)
    w index hi snapshot u padL padR hpre hL hR

theorem witness (sk : BitVec 256) (output : SigGolfCandidate.T3.HashOutput)
    (wit : SigGolfCandidate.Research.SharedForest.Witness) (nonces : List Nat)
    (index : Nat) (hi : index<2^31) (initial : MachineState)
    (h0 : OuterForestInv.Inv (OuterExpand.witEncOuter output wit nonces) index
      (SigGolfCandidate.Research.SharedForest.rawChildFromOutput output)
      (fun k=>SigGolfCandidate.Research.SharedForest.forestRank output k.val) initial 0
      (SharedV3.initialPair (OuterExpand.witEncOuter output wit nonces)) initial) :
    TBSim OuterImages.expandImage sk initial OuterForestRun.forestW
      (OuterForestCorrectness.recoverForest index
        (SigGolfCandidate.Research.SharedForest.forestSelectionFromOutput output)
        (SigGolfCandidate.Research.SharedForest.forestWordsFromOutput output) wit.signature.forest)
      (OuterForestRun.ForestPost initial index (SigGolfCandidate.Research.SharedForest.rawChildFromOutput output)
        (fun k=>SigGolfCandidate.Research.SharedForest.forestRank output k.val)) := by
  have hm:=run sk (OuterExpand.witEncOuter output wit nonces) index hi _ _ initial h0
  rw [OuterWitnessForest.forest output wit nonces index hi] at hm
  exact hm

#print axioms witness
#print axioms run
end OuterInstalledForest
