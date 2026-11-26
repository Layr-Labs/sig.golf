import SigGolfCandidate.OuterGroundFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterHeaderFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9

/-- C31: the two-word FTS node word of coordinate `c` has low half `0xF800 - 2048 c`. -/
theorem low16 (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat%65536=63488-2048*coord := by
  rw [ftsNodeWord_toNat]
  simp only [Nat.mod_eq_of_lt (show coord<16 by omega)]
  have := Nat.mod_lt index (show 0 < 2^31 by decide)
  unfold ftsBiasN
  omega

/-- C31: bits 11..15 of an FTS node word are `31 - coordinate`. -/
theorem coordField (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat/2048%32=31-coord := by
  have h := low16 coord index hc9
  omega

/-- C31: the low 11 bits of an FTS node word are zero. -/
theorem low11 (coord index : Nat) (hc9 : coord < 9) :
    (ftsNodeWord coord index).toNat%2048=0 := by
  have h := low16 coord index hc9
  omega

#print axioms low16
#print axioms coordField
end OuterHeaderFields
