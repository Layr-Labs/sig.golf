import SigGolfCandidate.T3.Secc.LargeCouplingQuery
import SigGolfCandidate.T3.Secc.LargeContactMonitor

namespace SigGolfCandidate.T3.Security.LargeCoupling
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3M SigGolfCandidate.T3M.Final SigGolfCandidate.T3M.SecurityInputs
  SigGolfCandidate.T3M.SecurityExtraction
open SigGolfCandidate.T3.Correctness (Answers)
open LargeResidual CanonGraph CanonEncoding
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
noncomputable local instance instDecidableEqCache_largeCouplingSigning : DecidableEq T3.Cache := Classical.decEq _
structure ReadsOnly {U : Finset HashInput} (τ : Cell U → HashOutput) (ws ws' : LargeResidual.State WCoord (Cell U)) :
    Prop where
  candidates : ws'.candidates = ws.candidates
  counters : ws'.counters = ws.counters
  rows : ∀ row v, ws'.rows row = some v → ws.rows row = some v ∨ (IsDigestRow row.val ∧ v = τ row)
theorem ReadsOnly.refl {U : Finset HashInput} (τ : Cell U → HashOutput) (ws : LargeResidual.State WCoord (Cell U)) :
    ReadsOnly τ ws ws :=
  ⟨rfl, rfl, fun _ _ h => Or.inl h⟩
theorem ReadsOnly.trans {U : Finset HashInput} {τ : Cell U → HashOutput} {ws ws' ws'' : LargeResidual.State WCoord (Cell U)}
    (h1 : ReadsOnly τ ws ws') (h2 : ReadsOnly τ ws' ws'') : ReadsOnly τ ws ws'' := by
  refine ⟨h2.candidates.trans h1.candidates, h2.counters.trans h1.counters, fun row v hv => ?_⟩
  rcases h2.rows row v hv with h | h
  · exact h1.rows row v h
  · exact Or.inr h
section Search
variable {U : Finset HashInput} (aux : (input : AuxSpec.Domain) → PMF (AuxSpec.Range input)) (q : Nat)
  (labels : WCoord → Digest) (τ : Cell U → HashOutput) (a : AuxData)
theorem digestRow_isDigest (rho : Digest) (m : Message) (c : BitVec 32) : IsDigestRow (pad64 (digestInput rho m c)) :=
  ⟨rho, m, c, rfl⟩
end Search
section Coherent
variable {U : Finset HashInput} {T : Answers} {vals : Coord → Digest} {nv : Message → Digest}
  {τ : Cell U → HashOutput} {a : AuxData}
theorem digestRow_mem (hUpub : SeccLaw.publicUniverse ⊆ U) (rho : Digest) (m : Message) (c : BitVec 32) :
    pad64 (digestInput rho m c) ∈ U := by
  apply hUpub
  apply SeccLaw.mem_publicUniverse
  have h := Wots.Ref.pad64_length_le (digestInput rho m c)
  have hl : (digestInput rho m c).length = 64 := by
    simp only [digestInput, List.length_append, SphincsSecurity.bytesLE_length]
  unfold SeccLaw.maxInputLength
  omega
theorem Coherent.privateNonce (hcoh : Coherent U T vals nv τ a) (m : Message) :
    evalWithAnswerFn T (T3.privateNonce m) = nv m := by
  simp only [T3.privateNonce, privateHash, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact hcoh.nonce m
theorem Coherent.signDigest (hcoh : Coherent U T vals nv τ a) (m : Message) :
    LargeResidual.signDigest T m = evalWithAnswerFn T (digestSearch (nv m) m 0 attemptLimit) := by
  unfold LargeResidual.signDigest
  rw [hcoh.privateNonce]
end Coherent
end SigGolfCandidate.T3.Security.LargeCoupling
