import SigGolfCandidate.ClaudeWCT_Numerics_N600PriceChecksRows

-- Keep the expensive row certificates in a reusable module; statements are unchanged.
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000
namespace ClaudeWCT.Numerics.N600
section
attribute [local irreducible] winsorRowDots poissonCheckQ
set_option backward.isDefEq.respectTransparency true
theorem winsor_mgf_ok : poissonCheckQ Q 13533529 100000000 LN LD
    (fun r => (winsorRowDots r).1) (3000*winsorScale*Nn^9) (3000*A) 1 8 1 80 = true := by
  have hf : (fun r => (winsorRowDots r).1) = (fun r => (winsorCertifiedDots r).1) :=
    funext fun r => congrArg Prod.fst (winsorRowDots_eq r)
  have h := congrArg (fun f => poissonCheckQ Q 13533529 100000000 LN LD f
    (3000*winsorScale*Nn^9) (3000*A) 1 8 1 80) hf
  exact h.trans winsor_mgf_fast_ok

theorem winsor_residual_ok : poissonCheckQ Q 13533529 100000000 LN LD
    (fun r => (winsorRowDots r).2) (winsorScale*Nn^9) A 1 1 5000 80 = true := by
  have hf : (fun r => (winsorRowDots r).2) = (fun r => (winsorCertifiedDots r).2) :=
    funext fun r => congrArg Prod.snd (winsorRowDots_eq r)
  have h := congrArg (fun f => poissonCheckQ Q 13533529 100000000 LN LD f
    (winsorScale*Nn^9) A 1 1 5000 80) hf
  exact h.trans winsor_residual_fast_ok
end
end ClaudeWCT.Numerics.N600


