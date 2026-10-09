import SigGolfCandidate.ClaudeWCT.WCT9.Basic

/-!
The FTS cost cap is attained by a producer-admissible digest. Its nine coordinate
costs are `92, 92, 92, 92, 92, 92, 83, 75, 75`, totaling 785. Therefore arithmetic
or a residue argument alone cannot lower the cap for all producer-admissible
digests. This does not assert that the full verification-cycle bound is attained.
-/

namespace SigGolfCandidate.Packaging.CostAudit

open ClaudeWCT.WCT9

def boundaryDigest : SigGolfCandidate.T3.HashOutput :=
  BitVec.ofNat 256 0x210541082af411881c8800e440800e401c8800e440000000000000e440

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem boundary_digest_facts :
    producerAdmissible boundaryDigest = true ∧
      jointCost boundaryDigest = jointCap ∧ jointCap = 785 := by
  decide +kernel

/-- Every uniform cap on producer-admissible FTS costs is at least 785. -/
theorem producer_cost_cap_minimum (cap : Nat)
    (h : ∀ output, producerAdmissible output = true → jointCost output ≤ cap) :
    785 ≤ cap := by
  have hb := h boundaryDigest boundary_digest_facts.1
  rw [boundary_digest_facts.2.1, boundary_digest_facts.2.2] at hb
  exact hb

end SigGolfCandidate.Packaging.CostAudit

#print axioms SigGolfCandidate.Packaging.CostAudit.boundary_digest_facts
#print axioms SigGolfCandidate.Packaging.CostAudit.producer_cost_cap_minimum
