import SigGolfCandidate.OuterSignNonceSearch
import SigGolfCandidate.OuterSignProgram
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignMachine
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 SigGolfCandidate.Research.SharedForest
open SigGolfCandidate.T3M.Sign SigGolfCandidate.T3M.Sign.Boundary
open SigGolfCandidate.T3M.Verify
open ClaudeWCT.W9.Machine.Sign

theorem forestLook : LookOK OuterImages.signImage SharedBoundary.forLook :=
  OuterSignLook.transfer _ SharedBoundary.installed_forLook (OuterSignLook.gap0 _ (by decide +kernel)) (by decide +kernel) (by decide +kernel) (by decide +kernel)

def work : Nat:=SigGolfCandidate.T3M.Sign.frontC+(1+((11*2^17)*200+20+OuterSignOutput.work))

theorem sign (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    TBSim OuterImages.signImage sk (sinit sk cache msg) work
      (OuterSigning.sign (cacheDec cache) msg) OuterSignCompleted.FinalPost := by
  rw [OuterSignProgram.sign_program]
  refine OuterSignNonceSearch.nonce_search
    (fun _ _ hn=>SharedDigest.tables_of_costAt (ClaudeWCT.W9.Machine.SignLink.hook_v7 hn).search.cost)
    (fun rho _ a=>OuterSignOutput.outputProgram cache rho a)
    (fun _ h=>h) ?_
  intro rho s hn c a t hj
  have hfront : HookPre sk msg rho s ∧ Base sk cache s ∧ s.getMem (BitVec.ofNat 64 (SigGolfCandidate.T3M.Sign.ENC+32))=0:=
    ⟨ClaudeWCT.W9.Machine.SignLink.hook_v7 hn,hn.inv⟩
  obtain ⟨hp,hb,hz⟩:=hfront
  obtain ⟨he,hb,hr,hz,hi,hranks⟩:=SharedState.digest_state hp hb hz hj
  exact OuterSignOutput.forest_tbsim OuterSignCoordinateCode.reuse OuterSignCoordinateCode.installed
    forestLook t he hb hr hz hi (ClaudeWCT.WCT9.digestIndex_lt a) hranks
#print axioms forestLook
#print axioms sign
end OuterSignMachine
