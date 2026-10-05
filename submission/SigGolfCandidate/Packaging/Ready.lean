import SigGolfCandidate.W9Fin.V4.Final
import SigGolfCandidate.W9Drv.Fts
import SigGolfCandidate.W9Machine.WctChainCertified
import SigGolfCandidate.W9Machine.WctImageIdentity
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.Final.Assembly
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert

section




namespace W9Fin.V4
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
def FtsOutV (pk : Digest) (w : WBytes) (a : HashOutput) (root : Digest) (u : MachineState) : Prop :=
  FtsOut ⟨pk, w, a⟩ root u
theorem goodQ_frozen {s : MachineState} {N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs} :
    W9Machine.GoodQFor W9Machine.Frozen.image s N C Q A X ↔ GoodQ s N C Q A X := by
  rw [W9Machine.Frozen.image_eq]; rfl
theorem fts_x5 : FtsGoodByCost W9Drv.GatePre FtsOutV
    (ftsAcceptCost 1118 ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost) := by
  intro pk w a u N C A Q K hu hK hnext
  have h := W9Drv.fts_good W9Machine.Chain.allGood pk w a u N C A Q K hu hK
    (fun root t ht => goodQ_frozen.mpr (hnext root t ht))
  exact goodQ_frozen.mp h
theorem after_x6 : AfterGoodBudget FtsOutV 5610 :=
  fun pk w Q hQ a root u h => SigGolfCandidate.T3M.after_good pk w Q hQ a root u h
theorem verify_final_closed :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I0 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I0 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I0 :=
  verify_inputs_x fts_x5 after_x6 (by unfold ClaudeWCT.W9.T3M.Final.verifyCycleBound; omega)
end W9Fin.V4
#print axioms W9Fin.V4.fts_x5
#print axioms W9Fin.V4.after_x6
#print axioms W9Fin.V4.verify_final_closed
end

section


namespace ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
theorem expand_pending (I : ClaudeWCT.W9.T3M.Images)
    (hv : I.expand.Valid (ClaudeWCT.W9.T3M.submission I).sizes (ClaudeWCT.W9.T3M.submission I).layout)
    (hc : NewCodeAt I.expand) (hF : FrontAt I.expand) (hd : ExpandDataOK I.expand) (hB : BackSpec I.expand) :
    ClaudeWCT.W9.T3M.Final.ExpandRefines I ∧ ClaudeWCT.W9.T3M.Final.ExpandTerminates I :=
  expandComposeSpec_holds (ClaudeWCT.W9.T3M.submission I).image hv hc hF hd hB
end ClaudeWCT.W9.Machine.Expand
namespace ClaudeWCT.W9.Machine.ExpandLink
open SigGolfCandidate.T3M
theorem expand_pending_v4 :
    ClaudeWCT.W9.T3M.Final.ExpandRefines I0 ∧ ClaudeWCT.W9.T3M.Final.ExpandTerminates I0 :=
  expand_W_v4
theorem sign_pending_v4 (hPacked : Sign.Packed.PackedLeafSpec ClaudeWCT.WCT9.buildLeafP) :
    ClaudeWCT.W9.T3M.Final.SignRefines I0 ∧ ClaudeWCT.W9.T3M.Final.SignTerminates I0 :=
  sign_W_v4 hPacked
theorem sign_pending_v4_closed :
    ClaudeWCT.W9.T3M.Final.SignRefines I0 ∧ ClaudeWCT.W9.T3M.Final.SignTerminates I0 :=
  sign_W_v4_closed
end ClaudeWCT.W9.Machine.ExpandLink
end

section






namespace SigGolfCandidate.Packaging
open ClaudeWCT.W9.Machine.ExpandLink (I0)
theorem certificate_ready :
    SigGolf.Certificate (SigGolfCandidate.Transfer.currentOf SigGolfCandidate.T3M.submission) 7547 :=
  ClaudeWCT.W9.Final.certificate_of_pending (I := I0)
    { large_route := ClaudeWCT.W9.T3.Security.LargeCoupling.large_route_hlarge
      pair_bound := ClaudeWCT.W9.T3.Security.WPair.pair_guess_bound
      near_bound := ClaudeWCT.W9.T3.Security.CaseC.nearBound
      admissible := SigGolfCandidate.T3M.submission_admissible
      verify_refines := W9Fin.V4.verify_final_closed.1
      verify_terminates := W9Fin.V4.verify_final_closed.2.1
      verify_accept_cycles := W9Fin.V4.verify_final_closed.2.2
      sign_refines := ClaudeWCT.W9.Machine.ExpandLink.sign_pending_v4_closed.1
      sign_terminates := ClaudeWCT.W9.Machine.ExpandLink.sign_pending_v4_closed.2
      expand_refines := ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v4.1
      expand_terminates := ClaudeWCT.W9.Machine.ExpandLink.expand_pending_v4.2 }
end SigGolfCandidate.Packaging
end
