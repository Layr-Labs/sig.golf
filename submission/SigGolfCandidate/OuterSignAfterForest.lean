import SigGolfCandidate.OuterSignPipeline
import SigGolfCandidate.OuterSignBuilt
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignAfterForest
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.SharedSearches
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
open ClaudeWCT.W9.T3M.SharedCodec

def layersProgram (cache : Bytes 131072) (rho : Digest) (index : Nat)
    (forest : ForestOpening×PairRoot) : SigGolfCandidate.T3.M (Option SharedSignature) := do
  let prepared←prepareRoots index
  let layers←OuterSigning.searchPreparedLayers (cacheDec cache) index prepared forest.2
  pure (layers.map (assemble rho forest.1))
def work : Nat:=13+((28+(2*Packed.btCost+3*47))+((prefixCost+335006)+(8549+34)))

theorem after_forest {sk : SecretKey} {cache : Bytes 131072} {cfFlag index : Nat}
    (hindex : index<2^31) {rho : Digest} {forest : ForestOpening×PairRoot}
    (s : MachineState) (hp : s.pc=pcOf 370) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 index)
    (hcounter : ∃c<2^32,s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=BitVec.ofNat 64 c)
    (hl : DigAt s ClaudeWCT.W9.Machine.Sign.FOUT forest.2.1) (hr : DigAt s (SigGolfCandidate.T3M.Sign.ENC+48) forest.2.2)
    (hfields : ForestFields rho forest.1 s) :
    TBSim OuterImages.signImage sk s work (layersProgram cache rho index forest) OuterSignCompleted.FinalPost := by
  have bridge:=OuterSignTransfers.code (b:=370) (by decide +kernel) SharedRootBridge.installed_code
  have flag:=OuterSignTransfers.code (b:=24661) (by decide +kernel) SharedFlagInit.installed_code
  obtain ⟨t,st,ht,ff⟩:=SharedRootBridge.bridge_steps bridge flag forest.2 s hp hb hi hcounter hl hr
  exact TBSim.steps st (OuterSignPipeline.prepared_serialize (OuterSignRoots.roots_good hindex ht)
    (fun p t h=>OuterSignBuilt.from_built_framed hindex h.1 ht.counter)
    (fun _ _ h=>h.2) (hfields.frame ff))
#print axioms after_forest
end OuterSignAfterForest
