import SigGolfCandidate.OuterGroundFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterHeaderFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- C46: the two-word FTS node word of coordinate `c` has low half `0xF800 - 2048 (c / 2)` (pairs share it). C47:
`0xF800 - 2048 ftsPair c` (coordinate 8 uses pair 3). -/
theorem low16 (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat%65536=63488-2048*ftsPair coord := by
  have h := ftsNodeWord_low16 coord index
  rw [show (2:Nat)^16=65536 by norm_num] at h
  exact h

/-- C46: bits 11..15 of an FTS node word are `31 - coordinate / 2`. C47: `31 - ftsPair coordinate`. -/
theorem coordField (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat/2048%32=31-ftsPair coord := by
  have h := low16 coord index hc9
  have hp := ftsPair_le coord
  omega

/-- C31: the low 11 bits of an FTS node word are zero. -/
theorem low11 (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat%2048=0 := by
  have h := low16 coord index hc9
  have hp := ftsPair_le coord
  omega

/-- C47: off coordinate 8 the pair is `coord / 2`. -/
theorem pair_of_ne (coord : Nat) (h8 : coord ≠ 8) : ftsPair coord = coord % 16 / 2 := ftsPair_of_ne h8

#print axioms low16
#print axioms coordField
end OuterHeaderFields
