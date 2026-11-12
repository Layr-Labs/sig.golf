import SigGolfCandidate.OuterGroundFresh
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterHeaderFields
open SigGolfCandidate.T3 ClaudeWCT.WCT9

theorem word_value (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31) :
    (ftsNodeWord coord index).toNat=63488+(coord-1)*65536+index*2^33 := by
  rw [ftsNodeWord_toNat]
  simp only [Nat.mod_eq_of_lt (show coord+1<16 by omega),Nat.mod_eq_of_lt hi]
  rw [ftsBiasN_eq _ (by omega),if_neg (by omega)]
  omega

theorem low16 (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31) :
    (ftsNodeWord coord index).toNat%65536=63488 := by
  rw [word_value coord index hc hc9 hi]
  omega

theorem coordNibble (coord index : Nat) (hc : 1 ≤ coord) (hc9 : coord < 9) (hi : index < 2^31) :
    (ftsNodeWord coord index).toNat/65536%16=coord-1 := by
  rw [word_value coord index hc hc9 hi]
  omega

#print axioms word_value
#print axioms coordNibble
end OuterHeaderFields
