import SigGolfCandidate.T3M.Images.Keygen
import Mathlib.Tactic.Ring

namespace ClaudeWCT.W9.T3M
open SigGolfCandidate.Legacy
structure Images where
  sign : Riscv.Image
  expand : Riscv.Image
  verify : Riscv.Image
def submission (I : Images) : Submission where
  sizes := ⟨5456, 21848, 131072⟩
  layout := ⟨0x5d68, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩
  image
    | .keygen => SigGolfCandidate.T3M.Images.keygenImage
    | .sign => I.sign
    | .expand => I.expand
    | .verify => I.verify
variable (I : Images)
@[simp] theorem submission_sizes : (submission I).sizes = ⟨5456, 21848, 131072⟩ := rfl
@[simp] theorem submission_layout : (submission I).layout = ⟨0x5d68, 0x80, 0xA0, 0x80000, 0x7000, 0x800⟩ := rfl
@[simp] theorem submission_keygen : (submission I).image .keygen = SigGolfCandidate.T3M.Images.keygenImage := rfl
@[simp] theorem submission_sign : (submission I).image .sign = I.sign := rfl
@[simp] theorem submission_expand : (submission I).image .expand = I.expand := rfl
@[simp] theorem submission_verify : (submission I).image .verify = I.verify := rfl

theorem two_pow_add (m n : Nat) : (2 : Nat) ^ (m + n) = (2 : Nat) ^ m * (2 : Nat) ^ n :=
  Nat.pow_add 2 m n

theorem bv_toNat_ofNat (n x : Nat) : (BitVec.ofNat n x).toNat = x % (2 : Nat) ^ n :=
  BitVec.toNat_ofNat x n

theorem bv_isLt {n : Nat} (x : BitVec n) : x.toNat < (2 : Nat) ^ n :=
  x.isLt

theorem bv_extractLsb'_toNat {n : Nat} (s m : Nat) (x : BitVec n) :
    (x.extractLsb' s m).toNat = x.toNat / (2 : Nat) ^ s % (2 : Nat) ^ m := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

@[irreducible] def powW : Nat := (2 : Nat) ^ (8 * 21832)
theorem powW_def : powW = (2 : Nat) ^ (8 * 21832) := by unfold powW; rfl
theorem powW_pos : 0 < powW := by rw [powW_def]; positivity
theorem powW_split : powW = (2 : Nat) ^ (8 * 21816) * (2 : Nat) ^ 128 := by
  have h : 8 * 21832 = 8 * 21816 + 128 := by decide
  exact (powW_def.trans (congrArg ((2 : Nat) ^ ·) h)).trans (two_pow_add (8 * 21816) 128)
theorem powW_mul128 : (2 : Nat) ^ (8 * 21848) = powW * (2 : Nat) ^ 128 := by
  have h : 8 * 21848 = 8 * 21832 + 128 := by decide
  exact (congrArg ((2 : Nat) ^ ·) h).trans ((two_pow_add (8 * 21832) 128).trans (congrArg (· * (2 : Nat) ^ 128) powW_def.symm))
theorem powW_ge2 (j : Nat) (h2 : 2 ≤ j) (hj : 8 * j < 21832) :
    ∃ K, powW = (2 : Nat) ^ 128 * ((2 : Nat) ^ (64 * (j - 2)) * ((2 : Nat) ^ 64 * K)) := by
  refine ⟨(2 : Nat) ^ (8 * 21832 - 64 * j - 64), ?_⟩
  have he : 8 * 21832 = 128 + (64 * (j - 2) + (64 + (8 * 21832 - 64 * j - 64))) := by omega
  exact (powW_def.trans (congrArg ((2 : Nat) ^ ·) he)).trans
    ((two_pow_add 128 _).trans (congrArg ((2 : Nat) ^ 128 * ·)
      ((two_pow_add (64 * (j - 2)) _).trans (congrArg ((2 : Nat) ^ (64 * (j - 2)) * ·)
        (two_pow_add 64 _)))))

def wProj (w : Bytes 21848) : Bytes 21832 :=
  BitVec.ofNat (8 * 21832) (w.toNat / powW % (2 : Nat) ^ 128 + (w.toNat % powW) / (2 : Nat) ^ 128 * (2 : Nat) ^ 128)
def wLift (wb : Bytes 21832) : Bytes 21848 :=
  BitVec.ofNat (8 * 21848) (wb.toNat + (wb.toNat % (2 : Nat) ^ 128) * powW)

theorem wProj_bound (X Y : Nat) (hX : X < (2 : Nat) ^ 128) (hY : Y < powW) :
    X + Y / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 < powW := by
  have hsplit := powW_split
  generalize hB : (2 : Nat) ^ 128 = B at hX hsplit ⊢
  generalize hC : (2 : Nat) ^ (8 * 21816) = C at hsplit
  rw [hsplit] at hY ⊢
  have hBpos : 0 < B := by subst hB; positivity
  have hdiv : Y / B < C := (Nat.div_lt_iff_lt_mul hBpos).mpr hY
  have hle : Y / B + 1 ≤ C := hdiv
  nlinarith

theorem wProj_toNat (w : Bytes 21848) :
    (wProj w).toNat = w.toNat / powW % (2 : Nat) ^ 128 + (w.toNat % powW) / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 := by
  unfold wProj
  rw [bv_toNat_ofNat, ← powW_def]
  exact Nat.mod_eq_of_lt (wProj_bound _ _ (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ powW_pos))

theorem wProj_mod128 (w : Bytes 21848) :
    (wProj w).toNat % (2 : Nat) ^ 128 = w.toNat / powW % (2 : Nat) ^ 128 := by
  rw [wProj_toNat, Nat.add_mul_mod_self_right, Nat.mod_mod]

theorem wProj_div128 (w : Bytes 21848) :
    (wProj w).toNat / (2 : Nat) ^ 128 = w.toNat % powW / (2 : Nat) ^ 128 := by
  rw [wProj_toNat, Nat.add_mul_div_right _ _ (by positivity),
    (Nat.div_eq_zero_iff_lt (by positivity)).mpr (Nat.mod_lt _ (by positivity)), Nat.zero_add]

theorem wProj_extract_ge2 (w : Bytes 21848) (j : Nat) (h2 : 2 ≤ j) (hj : 8 * j < 21832) :
    w.extractLsb' (64 * j) 64 = (wProj w).extractLsb' (64 * j) 64 := by
  obtain ⟨K, hK⟩ := powW_ge2 j h2 hj
  apply BitVec.eq_of_toNat_eq
  rw [bv_extractLsb'_toNat, bv_extractLsb'_toNat]
  have hj_eq : 64 * j = 128 + 64 * (j - 2) := by omega
  rw [congrArg ((2 : Nat) ^ ·) hj_eq, two_pow_add 128 (64 * (j - 2)),
    ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    wProj_div128, hK, Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self,
    Nat.mod_mul_right_mod]

theorem two_pow_128_eq : (2 : Nat) ^ 128 = (2 : Nat) ^ 64 * (2 : Nat) ^ 64 :=
  two_pow_add 64 64

theorem wProj_extract_0_aux (w : Bytes 21848) (k : Nat) (hk : (2 : Nat) ^ (64 * k) = powW) :
    w.extractLsb' (64 * k) 64 = (wProj w).extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_extractLsb'_toNat, bv_extractLsb'_toNat, hk, pow_zero, Nat.div_one,
    ← Nat.mod_mul_right_mod (wProj w).toNat ((2 : Nat) ^ 64) ((2 : Nat) ^ 64),
    ← two_pow_128_eq, wProj_mod128, two_pow_128_eq, Nat.mod_mul_right_mod]

theorem wProj_extract_0 (w : Bytes 21848) :
    w.extractLsb' (64 * 2729) 64 = (wProj w).extractLsb' (64 * 0) 64 := by
  have hk : (2 : Nat) ^ (64 * 2729) = powW :=
    (congrArg ((2 : Nat) ^ ·) (by decide : 64 * 2729 = 8 * 21832)).trans powW_def.symm
  exact wProj_extract_0_aux w 2729 hk

theorem wProj_extract_1_aux (w : Bytes 21848) (k : Nat) (hk : (2 : Nat) ^ (64 * k) = powW * (2 : Nat) ^ 64) :
    w.extractLsb' (64 * k) 64 = (wProj w).extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  rw [bv_extractLsb'_toNat, bv_extractLsb'_toNat, hk, ← Nat.div_div_eq_div_mul,
    ← Nat.mod_mul_right_div_self (wProj w).toNat ((2 : Nat) ^ 64) ((2 : Nat) ^ 64),
    ← two_pow_128_eq, wProj_mod128, two_pow_128_eq, Nat.mod_mul_right_div_self]

theorem wProj_extract_1 (w : Bytes 21848) :
    w.extractLsb' (64 * 2730) 64 = (wProj w).extractLsb' (64 * 1) 64 := by
  have hk : (2 : Nat) ^ (64 * 2730) = powW * (2 : Nat) ^ 64 :=
    (congrArg ((2 : Nat) ^ ·) (by decide : 64 * 2730 = 8 * 21832 + 64)).trans
      ((two_pow_add (8 * 21832) 64).trans (congrArg (· * (2 : Nat) ^ 64) powW_def.symm))
  exact wProj_extract_1_aux w 2730 hk

theorem wProj_wLift_aux (X : Nat) (hX : X < powW) :
    (X + X % (2 : Nat) ^ 128 * powW) % (powW * (2 : Nat) ^ 128) / powW % (2 : Nat) ^ 128 +
    ((X + X % (2 : Nat) ^ 128 * powW) % (powW * (2 : Nat) ^ 128) % powW) / (2 : Nat) ^ 128 * (2 : Nat) ^ 128 = X := by
  generalize hB : (2 : Nat) ^ 128 = B
  have hBpos : 0 < B := by subst hB; positivity
  have hApos := powW_pos
  have hlt2 : X + X % B * powW < powW * B := by
    have : X % B + 1 ≤ B := Nat.mod_lt _ hBpos
    nlinarith
  rw [Nat.mod_eq_of_lt hlt2, Nat.add_mul_div_right _ _ hApos,
    (Nat.div_eq_zero_iff_lt hApos).mpr hX, Nat.zero_add,
    Nat.mod_eq_of_lt (Nat.mod_lt _ hBpos), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hX]
  have := Nat.mod_add_div X B
  linarith

theorem wProj_wLift (wb : Bytes 21832) : wProj (wLift wb) = wb := by
  have hlt : wb.toNat < powW := powW_def.symm ▸ bv_isLt wb
  apply BitVec.eq_of_toNat_eq
  rw [wProj_toNat]
  unfold wLift
  rw [bv_toNat_ofNat, powW_mul128]
  exact wProj_wLift_aux wb.toNat hlt
end ClaudeWCT.W9.T3M
