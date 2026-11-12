import SigGolfCandidate.OuterSignAfterForest
import SigGolfCandidate.OuterSignForestState
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignOutput
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3M.Sign (Base ENC)
open ClaudeWCT.W9.Machine.Sign ClaudeWCT.W9.Machine.Sign.SharedSerializer
open ClaudeWCT.W9.T3M.SharedCodec

def outputProgram (cache : Bytes 131072) (rho : Digest) (a : BitVec 256) : SigGolfCandidate.T3.M (Option SharedSignature) := do
  let forest←OuterForestMoment.forest (ClaudeWCT.WCT9.digestIndex a) (forestSelectionFromOutput a) (forestWordsFromOutput a)
  OuterSignAfterForest.layersProgram cache rho (ClaudeWCT.WCT9.digestIndex a) forest

def work : Nat := (9*OuterSignForest.forestStepBound+23)+OuterSignAfterForest.work

theorem forest_tbsim {sk a : BitVec 256} {cache : Bytes 131072} {cfFlag : Nat} {rho : Digest}
    (hf : SharedReuse.Fetch OuterImages.signImage) (hc : ∀c,c<9→OuterSignCoordinateCode.Code c)
    (hl : LookOK OuterImages.signImage SharedBoundary.forLook)
    (s : MachineState) (hp : SharedCoordinate.Entry sk a s) (hb : Base (cfFlag:=cfFlag) sk cache s)
    (hrho : DigAt s SIG rho) (hz : s.getMem (BitVec.ofNat 64 (ENC+32))=0)
    (hi : s.getMem 0x20550=BitVec.ofNat 64 (ClaudeWCT.WCT9.digestIndex a))
    (hindex : ClaudeWCT.WCT9.digestIndex a<2^31)
    (hranks : ∀c,c<9→SharedCoordinate.rank c a<563) :
    TBSim OuterImages.signImage sk s work (outputProgram cache rho a) OuterSignCompleted.FinalPost := by
  refine TBSim.bind (OuterSignForestGood.forest_boundary_good hf hc hl hranks s hp) (W₂:=OuterSignAfterForest.work) ?_
  intro forest t ht
  exact OuterSignAfterForest.after_forest hindex t ht.pc (OuterSignForestState.base hb ht)
    ((OuterSignForestState.index ht).trans hi)
    ⟨0,by decide,by simpa using (OuterSignForestState.counter ht).trans hz⟩
    ht.rootLeft ht.rootRight ⟨OuterSignForestState.rho ht hrho,ht.values,ht.paths⟩

theorem outputProgram_source (cache : Bytes 131072) (rho : Digest) (c : BitVec 32) (a : BitVec 256) :
    (do let w←OuterSigning.signFromOutput (cacheDec cache) rho c a
        pure (w.map Witness.signature))=outputProgram cache rho a := by
  simp only [OuterSigning.signFromOutput,outputProgram,OuterSignAfterForest.layersProgram,bind_assoc]
  congr 1
  funext forest
  congr 1
  funext prepared
  congr 1
  funext layers
  cases layers <;> simp [assemble]
#print axioms forest_tbsim
#print axioms outputProgram_source
end OuterSignOutput
