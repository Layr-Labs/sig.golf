import SigGolfCandidate.OuterLooseSource
import SigGolfCandidate.OuterHashOnly
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterLooseBudget
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling SigGolfCandidate.T3.Cost SigGolfCandidate.T3.Freshness
open SigGolfCandidate.T3.Budgets (signingZ signingZ_pow)
open ClaudeWCT.W9.T3.PairRows
open ClaudeWCT.W9.T3.Freshness.Paired.GroundFresh

theorem V_sign_le_two (secret : BitVec 256) (cache : Cache) (message : Message) (rcache : RCache)
    (hs : AllSearchesFreshBC rcache) (hg : AllGFresh rcache) (hf : OuterGlobalFresh.AllFFresh rcache) :
    V secret signingZ (OuterLooseSource.signCompact cache message) rcache≤2 := by
  unfold OuterLooseSource.signCompact
  rw [V_map]
  exact OuterSigningEnvelope.V_sign_le_two secret cache message rcache hs hg hf

def honestSignCount (message : Message) : M (Option OuterSignatureCodec.NewSig×Nat) := do
  let keys←keygen
  countBlocks (OuterLooseSource.signCompact keys.2 message)

theorem honest_sign_exponential_budget (secret : BitVec 256) (message : Message) :
    expectedValue (roRun secret (honestSignCount message) ∅)
      (fun result=>(2:ENNReal)^((result.1.2:ℝ)/131072))≤2 := by
  rw [honestSignCount,roRun_bind,expectedValue_bind]
  apply expectedValue_le_of_support
  intro keys hkeys
  have h:=V_sign_le_two secret keys.1.2 message keys.2 (keygen_fresh_from_empty_bc secret keys hkeys)
    (keygen_allGFresh secret keys hkeys) (OuterGlobalFresh.keygen_allFFresh secret keys hkeys)
  simpa only [V,signingZ_pow] using h
#print axioms honest_sign_exponential_budget
end OuterLooseBudget
