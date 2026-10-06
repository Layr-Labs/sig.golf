import SigGolfCandidate.W9Fin.V4.InlinePrefixFinal
import SigGolfCandidate.T3M.Verify.Nonbinary.InlineAfter
import SigGolfCandidate.W9Drv.Fts
import SigGolfCandidate.W9Machine.WctChainCertified
import SigGolfCandidate.W9Machine.WctImageIdentity
import SigGolfCandidate.ClaudeWCT.W9.New.Machine.ExpandLink.Link
import SigGolfCandidate.ClaudeWCT.W9.Final.Assembly
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCNearFinal
import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.LargeCouplingCert

/- Select the actual native verifier; inherited sign/expand use their unchanged
   phase images. This is a source assembly awaiting kernel/server validation. -/
namespace W9Fin.V4.Inline
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M SigGolfCandidate.T3M.Verify
open SigGolfCandidate.T3 (Digest HashOutput)
def FtsOutV (pk : Digest) (w : WBytes) (a : HashOutput) (root : Digest) (u : MachineState) : Prop :=
  FtsOut ⟨pk, w, a⟩ root u

theorem goodQ_frozen {s : MachineState} {N C A : Nat} {Q : Prop} {X : OracleComp HashSpec Obs} :
    W9Machine.GoodQFor W9Machine.Frozen.image s N C Q A X ↔
      Nonbinary.InlineBudget.Judg.GoodQ Images.InlineNative.image s N C Q A X := by
  rw [W9Machine.Frozen.image_eq]
  rfl

theorem fts_native : FtsGoodByCost W9Drv.GatePre FtsOutV
    (ftsAcceptCost 1117 ClaudeWCT.WCT9.field ClaudeWCT.WCT9.routineCost) := by
  intro pk w a u N C A Q K hu hK hnext
  have h := W9Drv.fts_good W9Machine.Chain.allGood pk w a u N C A Q K hu hK
    (fun root t ht => goodQ_frozen.mpr (hnext root t ht))
  exact goodQ_frozen.mp h

theorem after_native : AfterGoodBudget FtsOutV 5600 := by
  intro pk w Q hQ a root u h
  exact Nonbinary.InlineTail.After.after_good pk w Q hQ a root u h

theorem verify_final_closed :
    ClaudeWCT.W9.T3M.Final.VerifyRefines I1 ∧ ClaudeWCT.W9.T3M.Final.VerifyTerminates I1 ∧
      ClaudeWCT.W9.T3M.Final.VerifyAcceptCycles I1 :=
  verify_inputs ⟨prefixGood, fts_native, after_native,
    by unfold ClaudeWCT.W9.T3M.Final.verifyCycleBound; omega⟩

theorem native_submission_eq : Native.submission = ClaudeWCT.W9.T3M.submission I1 := by
  rfl

#print axioms fts_native
#print axioms after_native
#print axioms verify_final_closed
end W9Fin.V4.Inline

namespace SigGolfCandidate.Packaging
open W9Fin.V4.Inline (I1)
theorem certificate_native_ready :
    SigGolf.Certificate (Transfer.currentOf T3M.Native.submission) 7529 := by
  have ha : (ClaudeWCT.W9.T3M.submission I1).Admissible := by
    rw [← W9Fin.V4.Inline.native_submission_eq]
    exact T3M.Native.submission_admissible
  have h := ClaudeWCT.W9.Final.certificate_of_pending (I := I1)
    { large_route := ClaudeWCT.W9.T3.Security.LargeCoupling.large_route_hlarge
      pair_bound := ClaudeWCT.W9.T3.Security.WPair.pair_guess_bound
      near_bound := ClaudeWCT.W9.T3.Security.CaseC.nearBound
      admissible := ha
      verify_refines := W9Fin.V4.Inline.verify_final_closed.1
      verify_terminates := W9Fin.V4.Inline.verify_final_closed.2.1
      verify_accept_cycles := W9Fin.V4.Inline.verify_final_closed.2.2
      sign_refines := ClaudeWCT.W9.Machine.ExpandLink.sign_W_v4_closed.1
      sign_terminates := ClaudeWCT.W9.Machine.ExpandLink.sign_W_v4_closed.2
      expand_refines := ClaudeWCT.W9.Machine.ExpandLink.expand_W_v4.1
      expand_terminates := ClaudeWCT.W9.Machine.ExpandLink.expand_W_v4.2 }
  simpa only [ClaudeWCT.W9.Final.submission, ClaudeWCT.W9.T3M.Final.submissionNew,
    ← W9Fin.V4.Inline.native_submission_eq] using h
#print axioms certificate_native_ready
end SigGolfCandidate.Packaging
