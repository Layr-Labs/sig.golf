import SigGolfCandidate.OuterSignSearchSteps
import SigGolfCandidate.OuterSignTopLeaf
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignLayers
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Search
open SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign.SharedSearches

theorem topCalls (sk : SecretKey) (cache : Bytes 131072) :
    TopCalls OuterImages.signImage sk cache := by
  constructor
  intro leaf hl ds u up hb hr h18 h25 hd ud
  have H:=SharedTopContinuation.top_only OuterSignSearchBindings.topBlocks
    OuterSignTopLeaf.continuation leaf hl ds u up hb hr h18 h25 hd ud
  exact H.mono (le_refl _) (by
    intro top t ht
    rcases ht with ⟨tp,tv,ta,tf,tm⟩
    exact ⟨tp,tv,ta,tf,tm _ (Or.inl rfl),tm _ (Or.inr rfl)⟩)

theorem layers {sk : SecretKey} {cache : Bytes 131072}
    (index : Nat) (hi : index<2^31) (p : PreparedRoots) (forest : BitVec 128×BitVec 128)
    (s : MachineState) (hp : s.pc=pcOf 22182) (hstable : Stable index p forest s)
    (hbase : SharedTopPath.StateBase sk cache s) (hh : s.getMem (0x66000#64)=0)
    (hc32 : ∃c<2^32,s.getMem (BitVec.ofNat 64 (Sign.ENC+32))=BitVec.ofNat 64 c) :
    TBSim OuterImages.signImage sk s (prefixCost+335006)
      (OuterSigning.searchPreparedLayers (cacheDec cache) index p forest)
      (OuterSignSearchSource.FramedLayersPost OuterImages.signImage index p s) :=
  OuterSignSearchSource.searchPreparedLayers_framed (topCalls sk cache)
    (OuterSignSearchSteps.searchCalls sk) OuterSignSearchSteps.topSetup OuterSignSearchSteps.topTail
    OuterSignSearchSteps.lowerSetup OuterSignSearchSteps.lowerTail OuterSignSearchSteps.finish
    index hi p forest s hp hstable hbase hh hc32
#print axioms topCalls
#print axioms layers
end OuterSignLayers
