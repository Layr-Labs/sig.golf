import SigGolfCandidate.SphincsSecurity_Proof_Hypertree_RootCache
import SigGolfCandidate.SphincsSecurity_Proof_Scheme_Secrets
import SigGolfCandidate.SphincsSecurity_Proof_Reference_SigningTrace
set_option Elab.async false

set_option autoImplicit true
namespace SphincsSecurity
open OracleComp OracleSpec
noncomputable def expandedAdversaryImpl (secretKey : SecretKey) :
    QueryImpl (OracleWorld + SigningSpec) (OracleComp OracleWorld) := by
  intro input
  cases input with
  | inl worldInput => exact liftM (OracleWorld.query worldInput)
  | inr request => exact Concrete.scheme.sign secretKey request
theorem forwardOracles_add_signingOracle_eq_withTraceAppend
    (secretKey : SecretKey) :
    forwardOracles + signingOracle Concrete.scheme secretKey =
      QueryImpl.withTraceAppend (expandedAdversaryImpl secretKey) signingLogFragment := by
  funext input
  cases input with
  | inl worldInput => rfl
  | inr request => rfl
theorem simulateQ_expandedAdversaryImpl_query_bind_inl
    (secretKey : SecretKey) (worldInput : OracleWorld.Domain)
    (continuation : OracleWorld.Range worldInput →
      OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftM ((OracleWorld + SigningSpec).query (.inl worldInput)) >>= continuation) =
      (liftM (OracleWorld.query worldInput) >>= fun output =>
        simulateQ (expandedAdversaryImpl secretKey) (continuation output)) := by
  simp [expandedAdversaryImpl]
theorem simulateQ_expandedAdversaryImpl_query_bind_inr
    (secretKey : SecretKey) (request : Message)
    (continuation : SigningSpec.Range request →
      OracleComp (OracleWorld + SigningSpec) α) :
    simulateQ (expandedAdversaryImpl secretKey)
        (liftM ((OracleWorld + SigningSpec).query (.inr request)) >>= continuation) =
      (Concrete.scheme.sign secretKey request >>= fun output =>
        simulateQ (expandedAdversaryImpl secretKey) (continuation output)) := by
  simp [expandedAdversaryImpl]
theorem unloggedMappedAdversaryImpl_eq_simulateQ_expanded
    (secretKey : SecretKey) (input : (OracleWorld + SigningSpec).Domain) :
    unloggedMappedAdversaryImpl secretKey input =
      simulateQ romImpl (expandedAdversaryImpl secretKey input) := by
  cases input with
  | inl worldInput =>
      exact (simulateQ_spec_query
        (impl := romImpl) worldInput).symm
  | inr request => rfl
namespace Concrete
end Concrete
end SphincsSecurity
