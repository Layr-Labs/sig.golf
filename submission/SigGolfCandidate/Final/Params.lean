/-!
# Iteration parameters

Optimized targets matching and beating the world record.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of accepting verify runs. -/
def verifyCycleBound : Nat := 7445

/-- The witness charge ⌈6348 / 256⌉. -/
def witnessCharge : Nat := 25

/-- The claimed verification cost C. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
