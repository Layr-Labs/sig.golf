import SigGolfCandidate.ClaudeWCT.Arith.GF128Inv
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.FinEnum
import ToMathlib.Data.BitVec

/-!
# GF(2^128) as `AdjoinRoot gcmPoly`, and the bridge from the bit-level arithmetic of `GF128.lean`

* `gcmPoly = X^128 + X^7 + X^2 + X + 1` over `ZMod 2`, `GF = AdjoinRoot gcmPoly` (a commutative ring; we never
  prove it is a field).
* `toPoly n` is the polynomial whose coefficient of `X^i` is bit `i` of `n`; `toGF a` is its class for a 128-bit `a`.
* `toGF_xor`, `toGF_mulPt` (for points `< 1024`), `toGF_bijective`: XOR is addition and `gfMulPt` is
  multiplication by the point, and `toGF` is a bijection `Digest → GF`.
* `point_sub_isUnit`: differences of distinct points `< 1024` are units, certified by the inverse table of
  `GF128Inv.lean` (no irreducibility proof).

`gcmPoly` is `@[irreducible]`: unfolding `X ^ 128` during unification exhausts the recursion limit.
-/

namespace ClaudeWCT.Arith
open SigGolfCandidate.T3 Polynomial


/-- The GCM modulus `X^128 + X^7 + X^2 + X + 1` over `ZMod 2`. -/
@[irreducible] noncomputable def gcmPoly : Polynomial (ZMod 2) := X ^ 128 + X ^ 7 + X ^ 2 + X + 1
theorem gcmPoly_monic : gcmPoly.Monic := by unfold gcmPoly; monicity!
theorem gcmPoly_natDegree : gcmPoly.natDegree = 128 := by unfold gcmPoly; compute_degree!
/-- GF(2^128) as the quotient ring `ZMod 2[X] / (gcmPoly)`. -/
abbrev GF := AdjoinRoot gcmPoly

/-- The bit polynomial of `n`: coefficient `i` is bit `i` of `n`. -/
noncomputable def toPoly (n : Nat) : Polynomial (ZMod 2) :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

theorem coeff_toPoly (n i : Nat) : (toPoly n).coeff i = if n.testBit i then 1 else 0 := by
  simp only [toPoly, finsetSum_coeff, apply_ite (fun p : (ZMod 2)[X] => p.coeff i), coeff_X_pow, coeff_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro hi
    simp only [Finset.mem_range, not_lt] at hi
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_right two_pos hi))]
    simp

theorem toPoly_xor (a b : Nat) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext i
  simp only [coeff_add, coeff_toPoly, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem toPoly_shiftLeft (a k : Nat) : toPoly (a <<< k) = X ^ k * toPoly a := by
  ext i
  rw [coeff_X_pow_mul', coeff_toPoly, coeff_toPoly, Nat.testBit_shiftLeft]
  by_cases h : k ≤ i <;> simp [h]

@[simp] theorem toPoly_zero : toPoly 0 = 0 := by
  ext i; simp [coeff_toPoly]

@[simp] theorem toPoly_one : toPoly 1 = 1 := by
  ext i; rw [coeff_toPoly, coeff_one]
  rcases i with _ | i
  · rfl
  · simp [Nat.testBit_succ]

theorem toPoly_split (c w : Nat) : toPoly c = toPoly (c % 2 ^ w) + X ^ w * toPoly (c >>> w) := by
  ext i
  rw [coeff_add, coeff_X_pow_mul', coeff_toPoly, coeff_toPoly, coeff_toPoly, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftRight]
  by_cases h : w ≤ i
  · simp [h, Nat.not_lt.2 h, Nat.add_sub_cancel' h]
  · simp [h, Nat.lt_of_not_le h]

theorem toPoly_mod_succ (d k : Nat) :
    toPoly (d % 2 ^ (k + 1)) = toPoly (d % 2 ^ k) + if d.testBit k then X ^ k else 0 := by
  ext i
  rw [coeff_add, coeff_toPoly, coeff_toPoly, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow,
    apply_ite (fun p : (ZMod 2)[X] => p.coeff i), coeff_X_pow, coeff_zero]
  rcases lt_trichotomy i k with h | rfl | h
  · simp [h, Nat.lt_succ_of_lt h, h.ne]
  · cases d.testBit i <;> simp
  · simp [h.ne', Nat.not_lt.2 h.le, Nat.not_lt.2 (Nat.succ_le_of_lt h)]

theorem toPoly_clmulSmall (a d k : Nat) : toPoly (clmulSmall a d k) = toPoly a * toPoly (d % 2 ^ k) := by
  induction k with
  | zero => simp [clmulSmall, Nat.mod_one]
  | succ k ih =>
    rw [clmulSmall, toPoly_xor, ih, toPoly_mod_succ, mul_add]
    split_ifs <;> simp [toPoly_shiftLeft, mul_comm, add_comm]

theorem toPoly_0x87 : toPoly 0x87 = X ^ 7 + X ^ 2 + X + 1 := by
  have : (0x87 : Nat) = (1 <<< 7) ^^^ (1 <<< 2) ^^^ (1 <<< 1) ^^^ 1 := rfl
  rw [this, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_shiftLeft, toPoly_shiftLeft, toPoly_shiftLeft]
  simp

theorem GF_two : (2 : GF) = 0 := by
  have h : ((2 : ZMod 2) : ZMod 2) = 0 := by decide
  rw [← map_ofNat (algebraMap (ZMod 2) GF) 2, h, map_zero]

theorem GF_add_self (x : GF) : x + x = 0 := by rw [← two_mul, GF_two, zero_mul]

theorem GF_neg (x : GF) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, GF_add_self]

theorem GF_sub (x y : GF) : x - y = x + y := by rw [sub_eq_add_neg, GF_neg]

theorem gcmPoly_eq : gcmPoly = X ^ 128 + (X ^ 7 + X ^ 2 + X + 1) := by
  unfold gcmPoly; rw [add_assoc (X ^ 128) (X ^ 7) (X ^ 2), add_assoc (X ^ 128) _ X, add_assoc (X ^ 128) _ 1]

theorem mk_X_pow_128 : AdjoinRoot.mk gcmPoly (X ^ 128) = AdjoinRoot.mk gcmPoly (X ^ 7 + X ^ 2 + X + 1) := by
  have h : AdjoinRoot.mk gcmPoly (X ^ 128 + (X ^ 7 + X ^ 2 + X + 1)) = 0 := by
    rw [← gcmPoly_eq]; exact AdjoinRoot.mk_self
  rw [map_add, add_eq_zero_iff_eq_neg, GF_neg] at h
  exact h

theorem mk_toPoly_gfFold (c : Nat) :
    AdjoinRoot.mk gcmPoly (toPoly (gfFold c)) = AdjoinRoot.mk gcmPoly (toPoly c) := by
  rw [gfFold, toPoly_xor, toPoly_clmulSmall, show (0x87 : Nat) % 2 ^ 8 = 0x87 by decide, toPoly_0x87,
    toPoly_split c 128, map_add, map_add, map_mul, map_mul, mk_X_pow_128, mul_comm]

theorem clmulSmall_lt {a n : Nat} (d k : Nat) (ha : a < 2 ^ n) : clmulSmall a d k < 2 ^ (n + k) := by
  induction k with
  | zero => simp [clmulSmall]
  | succ k ih =>
    rw [clmulSmall]
    apply Nat.xor_lt_two_pow
    · split_ifs
      · rw [Nat.shiftLeft_eq, ← Nat.add_assoc, Nat.pow_succ, Nat.pow_add]
        exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos k)) (by
          rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (by omega))
      · exact Nat.two_pow_pos _
    · exact lt_of_lt_of_le ih (Nat.pow_le_pow_right two_pos (by omega))

theorem gfFold_lt {c : Nat} (hc : c < 2 ^ 248) : gfFold c < 2 ^ 128 := by
  apply Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _))
  have : c >>> 128 < 2 ^ 120 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; exact hc)
  exact clmulSmall_lt 0x87 8 this

theorem gfMulSmall_lt {a d : Nat} (ha : a < 2 ^ 128) : gfMulSmall a d < 2 ^ 128 :=
  gfFold_lt (lt_of_lt_of_le (clmulSmall_lt d 10 ha) (Nat.pow_le_pow_right two_pos (by omega)))

/-- The field element of a 128-bit value: the class of its bit polynomial. -/
noncomputable def toGF (a : Digest) : GF := AdjoinRoot.mk gcmPoly (toPoly a.toNat)

theorem toGF_xor (a b : Digest) : toGF (a ^^^ b) = toGF a + toGF b := by
  rw [toGF, BitVec.toNat_xor, toPoly_xor, map_add]; rfl

@[simp] theorem toGF_zero : toGF 0 = 0 := by
  rw [toGF, show (0 : Digest).toNat = 0 from rfl, toPoly_zero, map_zero]

@[simp] theorem toGF_one : toGF 1 = 1 := by
  rw [toGF, show (1 : Digest).toNat = 1 from rfl, toPoly_one, map_one]

theorem toGF_ofNat {n : Nat} (h : n < 2 ^ 128) : toGF (BitVec.ofNat 128 n) = AdjoinRoot.mk gcmPoly (toPoly n) := by
  rw [toGF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem toGF_mulPt (a : Digest) {pt : Nat} (h : pt < 1024) :
    toGF (gfMulPt a pt) = toGF a * toGF (BitVec.ofNat 128 pt) := by
  rw [gfMulPt, toGF_ofNat (gfMulSmall_lt a.isLt), gfMulSmall, mk_toPoly_gfFold, toPoly_clmulSmall,
    Nat.mod_eq_of_lt (show pt < 2 ^ 10 by omega), map_mul, toGF_ofNat (by omega)]
  rfl

theorem degree_toPoly_lt {n : Nat} (h : n < 2 ^ 128) : (toPoly n).degree < ((128 : ℕ) : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_toPoly, Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right two_pos hi))]
  simp

theorem toGF_injective : Function.Injective toGF := by
  intro a b hab
  rw [toGF, toGF, AdjoinRoot.mk_eq_mk] at hab
  have hdeg : (toPoly a.toNat - toPoly b.toNat).degree < gcmPoly.degree := by
    rw [degree_eq_natDegree gcmPoly_monic.ne_zero, gcmPoly_natDegree]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt (degree_toPoly_lt a.isLt) (degree_toPoly_lt b.isLt))
  have h0 : toPoly a.toNat - toPoly b.toNat = 0 := eq_zero_of_dvd_of_degree_lt hab hdeg
  have h := sub_eq_zero.1 h0
  apply BitVec.eq_of_toNat_eq
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun p => Polynomial.coeff p i) h
  simp only [coeff_toPoly] at hi
  revert hi
  cases a.toNat.testBit i <;> cases b.toNat.testBit i <;> decide

theorem toGF_bijective : Function.Bijective toGF := by
  classical
  let pb := AdjoinRoot.powerBasis' gcmPoly_monic
  let e : GF ≃ (Fin pb.dim → ZMod 2) := pb.basis.equivFun.toEquiv
  let _ : Fintype GF := Fintype.ofEquiv _ e.symm
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨toGF_injective, ?_⟩
  rw [Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_fin, Fintype.card_bitVec]
  simp [pb, gcmPoly_natDegree]

/-- `toGF` as an equivalence. -/
noncomputable def gfEquiv : Digest ≃ GF := Equiv.ofBijective toGF toGF_bijective

theorem ofNat_xor {i j : Nat} (hi : i < 2 ^ 128) (hj : j < 2 ^ 128) :
    BitVec.ofNat 128 i ^^^ BitVec.ofNat 128 j = BitVec.ofNat 128 (i ^^^ j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hi hj)]

/-- Every nonzero point `d < 1024` is a unit of `GF` (inverse from `gfInvTable`). -/
theorem toGF_ofNat_isUnit {d : Nat} (h0 : 0 < d) (h : d < 1024) : IsUnit (toGF (BitVec.ofNat 128 d)) := by
  obtain ⟨e, he, hed⟩ := exists_gfInv h0 h
  refine IsUnit.of_mul_eq_one (toGF (BitVec.ofNat 128 e)) ?_
  rw [mul_comm, ← toGF_mulPt _ h, gfMulPt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt he, hed]
  exact toGF_one

/-- Distinct points below 1024 have a unit difference in `GF`. -/
theorem point_sub_isUnit {i j : Nat} (hi : i < 1024) (hj : j < 1024) (h : i ≠ j) :
    IsUnit (toGF (BitVec.ofNat 128 i) - toGF (BitVec.ofNat 128 j)) := by
  rw [GF_sub, ← toGF_xor, ofNat_xor (by omega) (by omega)]
  exact toGF_ofNat_isUnit (Nat.pos_of_ne_zero fun h0 => h (Nat.xor_eq_zero_iff.1 h0))
    (Nat.xor_lt_two_pow (n := 10) hi hj)

end ClaudeWCT.Arith
