import SigGolfCandidate.OuterGameTrace
import SigGolfCandidate.OuterSecurityGame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
namespace OuterPaddedGame
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3.Security.PairedOuter
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final.Paired
open ClaudeWCT.W9.T3M.Paired
open SigGolfCandidate.T3M (allQ_bind allQ_pure)
open SigGolfCandidate.Research.SharedForest (Signature)
set_option maxHeartbeats 200000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] keygen OuterSecurityGame.checkForgery
theorem check_public (publicKey : Digest) (log : QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) (forgery : OuterSecurityGame.Forgery) :
    SigGolfCandidate.T3.Security.PublicVerdict.Only (OuterSecurityGame.checkForgery publicKey log forgery) := by
  have hv (message : Message) (witness : WBytes) : SigGolfCandidate.T3.Security.PublicVerdict.Only (ClaudeWCT.W9.T3M.Paired.verifyP message publicKey witness) :=
    ClaudeWCT.W9.T3M.Paired.publicOnly_verifyP message publicKey witness
  have he (message : Message) (signature : SigGolfCandidate.Research.SharedForest.Signature) : SigGolfCandidate.T3.Security.PublicVerdict.Only (OuterRawExpand.expandB message publicKey signature) :=
    OuterRawExpand.publicOnly message publicKey signature
  cases forgery with
  | witness message witness =>
      unfold OuterSecurityGame.checkForgery
      exact allQ_bind (hv message witness) fun _ => allQ_pure _
  | signature message signature =>
      unfold OuterSecurityGame.checkForgery
      apply allQ_bind (he message signature)
      intro witness
      cases witness with
      | none => exact allQ_pure _
      | some witness => exact allQ_bind (hv message witness) fun _ => allQ_pure _
theorem check_nonMac (publicKey : Digest) (log : QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) (forgery : OuterSecurityGame.Forgery) :
    SigGolfCandidate.T3.Security.FullGame.NonMac (OuterSecurityGame.checkForgery publicKey log forgery) := by
  apply SigGolfCandidate.T3M.allQ_mono (check_public publicKey log forgery)
  intro input h
  rcases input with (sample | input) | coordinate
  · exact h.elim
  · trivial
  · exact h.elim
noncomputable def checker : OuterGameWith.Checker OuterSecurityGame.Forgery := ⟨OuterSecurityGame.checkForgery,check_nonMac⟩
theorem game_eq (adversary : OuterSecurityGame.Adversary) : OuterGameWith.game checker adversary=OuterSecurityGame.game adversary := by
  unfold OuterGameWith.game OuterSecurityGame.game
  apply bind_congr
  rintro ⟨publicKey,cache⟩
  unfold ClaudeWCT.W9.T3.Security.PairedOuter.FullGame.loggedWith OuterSecurityGame.signingOracle
  simp only [monadLift_self]
  apply bind_congr
  rintro ⟨forgery,log⟩
  cases forgery <;> rfl
theorem realExperiment_eq (adversary : OuterSecurityGame.Adversary) :
    OuterGameWith.realExperiment checker adversary=OuterSecurityGame.experiment adversary := by
  unfold OuterGameWith.realExperiment OuterSecurityGame.experiment
  rw [game_eq]
theorem verdict_public (publicKey : Digest) (result : Option OuterSecurityGame.Forgery × QueryLog ClaudeWCT.W9.T3.Security.PairedOuter.Requests) :
    SigGolfCandidate.T3.Security.PublicVerdict.Only (OuterGameWith.verdict checker publicKey result) := by
  unfold OuterGameWith.verdict
  cases result.1 with
  | none => exact allQ_pure _
  | some forgery => exact allQ_bind (check_public publicKey result.2 forgery) fun _ => allQ_pure _
abbrev TraceResult := Bool × (MonitoredPrivate.History × QueryRecorded.State)
noncomputable def tracedExperiment (adversary : OuterSecurityGame.Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    PMF TraceResult := OuterGameWith.Recorded.tracedExperiment checker adversary budget hbudget
theorem real_to_clean_trace (adversary : OuterSecurityGame.Adversary) (q : Nat) (hq : q ≤ 2^127) :
    Pr[fun result => result.1=true ∧ result.2 ≤ q | OuterSecurityGame.experiment adversary] ≤
      Pr[QueryRecorded.CleanWin q | tracedExperiment adversary q hq]+
      q/(2 : ENNReal)^146+((2 : ENNReal)^152)⁻¹+
      q/((2^256 : Nat) : ENNReal) := by
  simpa only [realExperiment_eq,tracedExperiment] using
    OuterGameWith.Recorded.real_to_clean_trace checker adversary q hq
theorem traced_record_erasure (adversary : OuterSecurityGame.Adversary) (budget : Nat) (hbudget : budget ≤ 2^127) :
    QueryRecorded.recordedTrace <$> tracedExperiment adversary budget hbudget=
      (liftM (FirstHit.record (OuterGameWith.idealGame checker adversary) (∅,∅)) : PMF _) :=
  OuterGameWith.Recorded.traced_record_erasure checker adversary budget hbudget
theorem traced_cost_coherent (adversary : OuterSecurityGame.Adversary) (budget : Nat) (hbudget : budget ≤ 2^127)
    (result : TraceResult) (hr : result ∈ (tracedExperiment adversary budget hbudget).support) :
    QueryRecorded.CostCoherent result.2.2 :=
  OuterGameWith.Recorded.traced_cost_coherent checker adversary budget hbudget result hr

#print axioms real_to_clean_trace
end OuterPaddedGame
