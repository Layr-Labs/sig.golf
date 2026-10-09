import SigGolfCandidate.T3.Core

/-!
# GF(2^128) arithmetic and polynomial seed families (arithmetic chain seeds)

Field: GF(2)[X] / (X^128 + X^7 + X^2 + X + 1) (the GCM polynomial). A 128-bit value `a` stands for the polynomial
whose coefficient of `X^i` is bit `i` of `a`. Seeds of a family are `familyEval coefs pt`, the Horner evaluation of
the polynomial with coefficients `coefs` (constant term first) at the small point `pt < 1024`, read as a polynomial
of degree < 10. Only multiplication by such small points is needed, so `gfMulSmall` folds once.
-/

namespace ClaudeWCT.Arith
open SigGolfCandidate.T3

/-- Carry-less product of `a` by the low `fuel` bits of `d`. -/
def clmulSmall (a d : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (if d.testBit k then a <<< k else 0) ^^^ clmulSmall a d k

/-- One fold of the bits at and above 128 with `X^128 = X^7 + X^2 + X + 1` (enough for products below 2^245). -/
def gfFold (c : Nat) : Nat := (c % 2 ^ 128) ^^^ clmulSmall (c >>> 128) 0x87 8

/-- Product in GF(2^128) of `a < 2^128` by a point `d < 1024`. -/
def gfMulSmall (a d : Nat) : Nat := gfFold (clmulSmall a d 10)

/-- Product of a 128-bit value by a small point. -/
def gfMulPt (a : Digest) (pt : Nat) : Digest := BitVec.ofNat 128 (gfMulSmall a.toNat pt)

/-- Horner evaluation in GF(2^128) at `pt`: `coefs = [c0, c1, ..., cm]` gives `c0 + pt·(c1 + pt·(... cm))`. -/
def familyEval (coefs : List Digest) (pt : Nat) : Digest :=
  coefs.foldr (fun c acc => gfMulPt acc pt ^^^ c) 0

example : gfMulSmall 5 3 = 15 := by decide
example : familyEval [1#128, 2#128] 3 = 7#128 := by decide

end ClaudeWCT.Arith
