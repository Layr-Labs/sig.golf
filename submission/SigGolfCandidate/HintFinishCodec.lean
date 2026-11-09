import SigGolfCandidate.HintSignFinish
import SigGolfCandidate.Merge045
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace SigGolfCandidate.HintSignFinish
open SigGolfCandidate.T3 ClaudeWCT.W9.T3M.SharedCodec
open SigGolfCandidate.Legacy RiscvZkvm.Rv64
 theorem codec_x (sig : SharedSignature) (h : Word) (hh : h.setWidth 16 = sig.policyHints)
    (he : sig.policyHints.toNat / 484 % 2 = 0) :
    (newX (((sigDigests sig).getD 176 0).extractLsb' 0 64)
      (((sigDigests sig).getD 176 0).extractLsb' 64 64) h).toNat = xField sig := by
  have hv : h.toNat % 2^16 = sig.policyHints.toNat := by
    have hv := congrArg BitVec.toNat hh
    simpa only [BitVec.toNat_setWidth] using hv
  rw [newX_toNat,hintCalc_toNat,hv,formula_compress _ he]
  unfold xField
  simp only [BitVec.extractLsb'_toNat,Nat.shiftRight_eq_div_pow,Nat.zero_add,Nat.pow_zero,Nat.div_one]
  have hm := ((sigDigests sig).getD 176 0).isLt
  norm_num at hm ⊢
  omega
 theorem floors_even (f1 f2 f3 : Nat) (h1 : f1 < 16) (h2 : f2 < 22) (h3 : f3 < 22)
    (he : f1 % 2 = 0) : ((484*f1+22*f2+f3)%2^16)/484%2=0 := by
  have hs : 22*f2+f3<484 := by omega
  have ht : 484*f1+22*f2+f3<65536 := by omega
  rw [show (2:Nat)^16=65536 by decide,Nat.mod_eq_of_lt ht]
  have hd : (484*f1+22*f2+f3)/484=f1 := by omega
  rw [hd]
  exact he

end SigGolfCandidate.HintSignFinish
