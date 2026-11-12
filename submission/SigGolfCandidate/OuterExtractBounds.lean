import SigGolfCandidate.OuterNodeReferenceAll
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option Elab.async false
namespace OuterExtractBounds

theorem level (coord layer : Nat) (h : OuterExtractGround.ftsNonceLevel coord layer) :
    2≤layer ∧ layer≤5 := by
  rcases h with h|h
  · unfold ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel at h
    omega
  · omega
theorem used (coord layer : Nat) (h : OuterExtractGround.ftsNonceLevel coord layer)
    (hf : coord<8 ∧ coord%2=0) : layer<5 := by
  rcases h with h|⟨he,hn⟩
  · unfold ClaudeWCT.W9.T3M.Extract.Paired.ftsNonceLevel at h;omega
  · have ht : ClaudeWCT.W9.T3M.Extract.Paired.first coord=true:=by
      exact decide_eq_true hf
    rw [ht] at hn
    cases hn
#print axioms level
end OuterExtractBounds
