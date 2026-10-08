import SigGolfCandidate.ClaudeWCT.WCT9.Core
import SigGolfCandidate.T3.Nonbinary.LowerLayout

section


namespace ClaudeWCT.WCT9
open SigGolfCandidate.T3
def decodeV5Lower (lay : Layer) (n : Nat) : Option (List Nat) :=
  if n ≥ 2 ^ 126 then none else
  let digits := (List.range 42).map fun i => n / 2 ^ (3 * i) % 8
  let total := digits.sum
  if total ≤ target lay ∧ target lay - total < 8 then some (digits ++ [target lay - total]) else none
def producerDecodeV5Lower (lay : Layer) (n : Nat) : Option (List Nat) :=
  (decodeV5Lower lay n).bind fun digits => if producerFloor lay ≤ wordCredit lay digits then some digits else none
theorem producerDecode_eq_bind (lay : Layer) (v : Digest) :
    producerDecode lay v =
      (decode lay v).bind fun digits => if producerFloor lay ≤ wordCredit lay digits then some digits else none := by
  unfold producerDecode
  generalize decode lay v = x
  cases x <;> rfl
theorem decode_lower_eq {lay : Layer} (hlay : lay ≠ 0) (v : Digest) :
    decode lay v = if lowerSpare v then decodeV5Lower lay (lowerWord v) else none := by
  have hw := lowerWord_lt v
  rw [decode_lowerWord hlay v]
  unfold decodeV5Lower
  rw [if_neg (show ¬ lowerWord v ≥ 2 ^ 126 by omega)]
  dsimp only
  by_cases hs : lowerSpare v
  · rw [if_pos hs]
    by_cases hc : ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum ≤ target lay ∧
        target lay - ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum < 8
    · rw [if_pos ⟨hs, hc⟩, if_pos hc]
    · rw [if_neg (fun h => hc h.2), if_neg hc]
  · rw [if_neg hs, if_neg (fun h => hs h.1)]
theorem producerDecode_lower_eq {lay : Layer} (hlay : lay ≠ 0) (v : Digest) :
    producerDecode lay v = if lowerSpare v then producerDecodeV5Lower lay (lowerWord v) else none := by
  rw [producerDecode_eq_bind, decode_lower_eq hlay]
  by_cases hs : lowerSpare v
  · rw [if_pos hs, if_pos hs]
    rfl
  · rw [if_neg hs, if_neg hs]
    rfl
theorem decode_lowerPack {lay : Layer} (hlay : lay ≠ 0) {n : Nat} (hn : n < 2 ^ 126) :
    decode lay (lowerPack n) = decodeV5Lower lay n := by
  rw [decode_lower_eq hlay, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn]
theorem producerDecode_lowerPack {lay : Layer} (hlay : lay ≠ 0) {n : Nat} (hn : n < 2 ^ 126) :
    producerDecode lay (lowerPack n) = producerDecodeV5Lower lay n := by
  rw [producerDecode_lower_eq hlay, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn]
def lowerEquiv : {n : Nat // n < 2 ^ 126} ≃ {v : Digest // lowerSpare v} where
  toFun n := ⟨lowerPack n.val, lowerSpare_lowerPack n.val⟩
  invFun v := ⟨lowerWord v.val, lowerWord_lt v.val⟩
  left_inv n := Subtype.ext (lowerWord_lowerPack n.property)
  right_inv v := Subtype.ext (lowerPack_lowerWord v.property)
theorem card_lower_transfer (f : Digest → Option (List Nat)) (g : Nat → Option (List Nat))
    (hf : ∀ v, f v = if lowerSpare v then g (lowerWord v) else none)
    (P : Option (List Nat) → Prop) [DecidablePred P] (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (f v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (g n)).card := by
  have hs : ∀ v, P (f v) → lowerSpare v ∧ P (g (lowerWord v)) := by
    intro v hv
    rw [hf] at hv
    by_cases h : lowerSpare v
    · rw [if_pos h] at hv; exact ⟨h, hv⟩
    · rw [if_neg h] at hv; exact absurd hv hP
  refine Finset.card_bij' (fun v _ => lowerWord v) (fun n _ => lowerPack n) ?_ ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    exact ⟨Finset.mem_range.mpr (lowerWord_lt v), (hs v hv.2).2⟩
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_filter, hf, if_pos (lowerSpare_lowerPack n), lowerWord_lowerPack hn.1]
    exact ⟨Finset.mem_univ _, hn.2⟩
  · intro v hv
    rw [Finset.mem_filter] at hv
    exact lowerPack_lowerWord (hs v hv.2).1
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_range] at hn
    exact lowerWord_lowerPack hn.1
theorem card_decode_lower {lay : Layer} (hlay : lay ≠ 0) (P : Option (List Nat) → Prop) [DecidablePred P]
    (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (decode lay v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (decodeV5Lower lay n)).card :=
  card_lower_transfer (decode lay) (decodeV5Lower lay) (decode_lower_eq hlay) P hP
theorem card_producerDecode_lower {lay : Layer} (hlay : lay ≠ 0) (P : Option (List Nat) → Prop) [DecidablePred P]
    (hP : ¬ P none) :
    (Finset.univ.filter fun v : Digest => P (producerDecode lay v)).card =
      ((Finset.range (2 ^ 126)).filter fun n => P (producerDecodeV5Lower lay n)).card :=
  card_lower_transfer (producerDecode lay) (producerDecodeV5Lower lay) (producerDecode_lower_eq hlay) P hP
end ClaudeWCT.WCT9
end

section



namespace SigGolfCandidate.T3M
open SigGolfCandidate.T3
theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]
theorem split3 (n M : Nat) : n &&& (64 * M + 7) = 64 * ((n / 64) &&& M) + n % 8 :=
  land_split n M 3 6 (by decide)
theorem split6 (n M : Nat) : n &&& (4096 * M + 63) = 4096 * ((n / 4096) &&& M) + n % 64 :=
  land_split n M 6 12 (by decide)
theorem split2 (n M : Nat) : n &&& (16 * M + 3) = 16 * ((n / 16) &&& M) + n % 4 :=
  land_split n M 2 4 (by decide)
theorem split4 (n M : Nat) : n &&& (256 * M + 15) = 256 * ((n / 256) &&& M) + n % 16 :=
  land_split n M 4 8 (by decide)
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4
theorem and3 (n : Nat) : n &&& 3 = n % 4 := Nat.and_two_pow_sub_one_eq_mod n 2
def mask3 : Nat := 8198552921648689607
def mask6 : Nat := 17311559823019733055
def mask2 : Nat := 3689348814741910323
def mask4 : Nat := 1085102592571150095
theorem landM1 (n : Nat) : n &&& mask3 =
    64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 % 8) + n / 64 / 64 % 8) + n / 64 % 8) + n % 8 := by
  rw [show mask3 = 64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * 7 + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7 by
    norm_num [mask3]]
  simp only [split3, and7]
theorem landM2 (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 4096 / 4096 / 4096 / 4096 / 4096 % 16)
    + n / 4096 / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 % 64)
    + n / 4096 % 64) + n % 64 := by
  rw [show mask6 = 4096 * (4096 * (4096 * (4096 * (4096 * 15 + 63) + 63) + 63) + 63) + 63 by norm_num [mask6]]
  simp only [split6, and15]
def sw1 (a b : Nat) : Nat :=
  ((((a / 8 &&& mask3) + (a &&& mask3)) % 18446744073709551616 + (b / 8 &&& mask3)) % 18446744073709551616 +
    (b &&& mask3)) % 18446744073709551616
def lowSwar (a b : Nat) : Nat := ((sw1 a b + sw1 a b / 64) % 18446744073709551616 &&& mask6) % 4095
theorem hdiv64 (c R : Nat) (h : c < 64) : (c + 64 * R) / 64 = R := by omega
theorem hmod64 (c R : Nat) (h : c < 64) : (c + 64 * R) % 64 = c := by omega
theorem landM2' (n : Nat) : n &&& mask6 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 16)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 / 64 / 64 / 64 / 64 % 64)
    + n / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 % 64) + n % 64 := by
  rw [landM2]; simp only [Nat.div_div_eq_div_mul]
theorem fold_mod4095 (a b c d e f : Nat) :
    (a + 4096 * (b + 4096 * (c + 4096 * (d + 4096 * (e + 4096 * f))))) % 4095 =
      (a + b + c + d + e + f) % 4095 := by
  omega
theorem swarLanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 : Nat) (h0 : L0 ≤ 28) (h1 : L1 ≤ 28) (h2 : L2 ≤ 28)
    (h3 : L3 ≤ 28) (h4 : L4 ≤ 28) (h5 : L5 ≤ 28) (h6 : L6 ≤ 28) (h7 : L7 ≤ 28) (h8 : L8 ≤ 28) (h9 : L9 ≤ 28)
    (h10 : L10 ≤ 15) (X : Nat)
    (hX : X = L0 + 64 * (L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))))) :
    ((X + X / 64) % 18446744073709551616 &&& mask6) % 4095 =
      L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 := by
  have e1 : X / 64 = L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 +
      64 * (L9 + 64 * L10)))))))) := by rw [hX]; exact hdiv64 _ _ (by omega)
  have e2 : X + X / 64 = (L0 + L1) + 64 * ((L1 + L2) + 64 * ((L2 + L3) + 64 * ((L3 + L4) + 64 * ((L4 + L5) +
      64 * ((L5 + L6) + 64 * ((L6 + L7) + 64 * ((L7 + L8) + 64 * ((L8 + L9) + 64 * ((L9 + L10) +
      64 * L10))))))))) := by
    omega
  have e3 : X + X / 64 < 18446744073709551616 := by rw [e2]; omega
  have e4 : (X + X / 64) % 18446744073709551616 &&& mask6 = (L0 + L1) + 4096 * ((L2 + L3) + 4096 * ((L4 + L5) +
      4096 * ((L6 + L7) + 4096 * ((L8 + L9) + 4096 * L10)))) := by
    rw [Nat.mod_eq_of_lt e3, e2, landM2']
    simp (disch := omega) only [hdiv64, hmod64]
    rw [Nat.mod_eq_of_lt (show L10 < 16 by omega)]
    omega
  rw [e4]
  clear e1 e2 e3 e4 hX
  have hlt : L0 + L1 + (L2 + L3) + (L4 + L5) + (L6 + L7) + (L8 + L9) + L10 < 4095 := by omega
  rw [fold_mod4095, Nat.mod_eq_of_lt hlt]
  ac_rfl
def dsum21 (a : Nat) : Nat :=
  a % 8 + a / 8 % 8 + a / 64 % 8 + a / 512 % 8 + a / 4096 % 8 + a / 32768 % 8 + a / 262144 % 8 +
    a / 2097152 % 8 + a / 16777216 % 8 + a / 134217728 % 8 + a / 1073741824 % 8 +
    a / 8589934592 % 8 + a / 68719476736 % 8 + a / 549755813888 % 8 + a / 4398046511104 % 8 +
    a / 35184372088832 % 8 + a / 281474976710656 % 8 + a / 2251799813685248 % 8 +
    a / 18014398509481984 % 8 + a / 144115188075855872 % 8 + a / 1152921504606846976 % 8
theorem dsum21_eq (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 8 ^ i % 8).sum := by
  simp only [dsum21, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num [Nat.add_assoc]
theorem lowSwar_eq (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 63) :
    lowSwar a b = dsum21 a + a / 2 ^ 63 + dsum21 b := by
  have hat : a / 9223372036854775808 ≤ 1 := by omega
  have ha' : a / 9223372036854775808 % 8 = a / 9223372036854775808 := Nat.mod_eq_of_lt (by omega)
  have hb' : b / 9223372036854775808 = 0 := Nat.div_eq_of_lt hb
  unfold lowSwar dsum21
  generalize hX : sw1 a b = X
  unfold sw1 at hX
  simp only [landM1, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  rw [ha'] at hX
  simp only [hb', Nat.zero_mod, Nat.mul_zero] at hX
  norm_num
  clear ha'
  generalize a / 9223372036854775808 = a21 at *
  have ha0 : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a % 8 = a0 at *
  have ha1 : a / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8 % 8 = a1 at *
  have ha2 : a / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 8 = a2 at *
  have ha3 : a / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 512 % 8 = a3 at *
  have ha4 : a / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 8 = a4 at *
  have ha5 : a / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 32768 % 8 = a5 at *
  have ha6 : a / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 8 = a6 at *
  have ha7 : a / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2097152 % 8 = a7 at *
  have ha8 : a / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 8 = a8 at *
  have ha9 : a / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 134217728 % 8 = a9 at *
  have ha10 : a / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 8 = a10 at *
  have ha11 : a / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8589934592 % 8 = a11 at *
  have ha12 : a / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 8 = a12 at *
  have ha13 : a / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 549755813888 % 8 = a13 at *
  have ha14 : a / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 8 = a14 at *
  have ha15 : a / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 35184372088832 % 8 = a15 at *
  have ha16 : a / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 8 = a16 at *
  have ha17 : a / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2251799813685248 % 8 = a17 at *
  have ha18 : a / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 8 = a18 at *
  have ha19 : a / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 144115188075855872 % 8 = a19 at *
  have ha20 : a / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 8 = a20 at *
  have hb0 : b % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b % 8 = b0 at *
  have hb1 : b / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8 % 8 = b1 at *
  have hb2 : b / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 8 = b2 at *
  have hb3 : b / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 512 % 8 = b3 at *
  have hb4 : b / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 8 = b4 at *
  have hb5 : b / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 32768 % 8 = b5 at *
  have hb6 : b / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 8 = b6 at *
  have hb7 : b / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2097152 % 8 = b7 at *
  have hb8 : b / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 8 = b8 at *
  have hb9 : b / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 134217728 % 8 = b9 at *
  have hb10 : b / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 8 = b10 at *
  have hb11 : b / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8589934592 % 8 = b11 at *
  have hb12 : b / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 8 = b12 at *
  have hb13 : b / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 549755813888 % 8 = b13 at *
  have hb14 : b / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 8 = b14 at *
  have hb15 : b / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 35184372088832 % 8 = b15 at *
  have hb16 : b / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 8 = b16 at *
  have hb17 : b / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2251799813685248 % 8 = b17 at *
  have hb18 : b / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 8 = b18 at *
  have hb19 : b / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 144115188075855872 % 8 = b19 at *
  have hb20 : b / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 8 = b20 at *
  clear ha hb hb'
  rw [swarLanes (a0 + a1 + b0 + b1) (a2 + a3 + b2 + b3) (a4 + a5 + b4 + b5) (a6 + a7 + b6 + b7)
    (a8 + a9 + b8 + b9) (a10 + a11 + b10 + b11) (a12 + a13 + b12 + b13) (a14 + a15 + b14 + b15)
    (a16 + a17 + b16 + b17) (a18 + a19 + b18 + b19) (a20 + a21 + b20) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega)
    (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) (by clear hX; omega) X (by
    rw [← hX]
    clear hX
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  clear hX
  ac_rfl
theorem div_mod_add_pow (x y k m w : Nat) (h : k + w ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k % 2 ^ w = x / 2 ^ k % 2 ^ w := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ w * (2 ^ (m - k - w) * y)) := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.add_mul_mod_self_left]
theorem div_add_pow (x y k m : Nat) (h : k ≤ m) :
    (x + 2 ^ m * y) / 2 ^ k = x / 2 ^ k + 2 ^ (m - k) * y := by
  have e : 2 ^ m * y = 2 ^ k * (2 ^ (m - k) * y) := by
    rw [← Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (Nat.two_pow_pos k)]
theorem dig_carry (b c j : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) (hj : 0 < j) :
    (b + c) / 2 ^ (3 * j) % 8 = b / 2 ^ (3 * j) % 8 := by
  have e : (b + c) / 2 = b / 2 := by omega
  have p : 2 ^ (3 * j) = 2 * 2 ^ (3 * j - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  rw [p, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e]
theorem dig_carry0 (b c : Nat) (hb : b % 2 = 0) (hc : c ≤ 1) : (b + c) % 8 = b % 8 + c := by omega
theorem sum_range_add (f : Nat → Nat) (m n : Nat) :
    ((List.range (m + n)).map f).sum = ((List.range m).map f).sum + ((List.range n).map fun j => f (m + j)).sum := by
  rw [List.range_add, List.map_append, List.sum_append, List.map_map]
  rfl
theorem sum_range_succ' (f : Nat → Nat) (n : Nat) :
    ((List.range (n + 1)).map f).sum = f 0 + ((List.range n).map fun j => f (j + 1)).sum := by
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  rfl
theorem sum_congr_range (f g : Nat → Nat) (n : Nat) (h : ∀ i < n, f i = g i) :
    ((List.range n).map f).sum = ((List.range n).map g).sum := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h i (List.mem_range.mp hi)
theorem dsum21_pow (a : Nat) : dsum21 a = ((List.range 21).map fun i => a / 2 ^ (3 * i) % 2 ^ 3).sum := by
  rw [dsum21_eq]
  apply sum_congr_range
  intro i _
  rw [Nat.pow_mul]; rfl
theorem lowDigits_sum (v0 v1 : Nat) (h0 : v0 < 2 ^ 64) :
    ((List.range 42).map fun i => (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3).sum =
      dsum21 v0 + v0 / 2 ^ 63 + dsum21 (2 * v1) := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * i) % 2 ^ 3 = v0 / 2 ^ (3 * i) % 2 ^ 3 :=
    fun i hi => div_mod_add_pow _ _ _ _ _ (by omega)
  rw [sum_congr_range _ _ 21 hlow]
  have hc : v0 / 2 ^ 63 ≤ 1 := by
    have : v0 / 2 ^ 63 < 2 := Nat.div_lt_of_lt_mul (by rw [show 2 ^ 63 * 2 = 2 ^ 64 by norm_num]; exact h0)
    omega
  have hW : ∀ j, (v0 + 2 ^ 64 * v1) / 2 ^ (3 * (21 + j)) % 2 ^ 3 = (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8 := by
    intro j
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (by omega)]
    norm_num
    rw [Nat.add_comm]
  simp only [hW]
  have e1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
      v0 / 2 ^ 63 + ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum := by
    have s1 : ((List.range 21).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8).sum =
        (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * 0) % 8 +
          ((List.range 20).map fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8).sum :=
      sum_range_succ' (fun j => (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * j) % 8) 20
    have s2 : ((List.range 21).map fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3).sum =
        2 * v1 / 2 ^ (3 * 0) % 2 ^ 3 + ((List.range 20).map fun j => 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3).sum :=
      sum_range_succ' (fun j => 2 * v1 / 2 ^ (3 * j) % 2 ^ 3) 20
    have hj : ∀ j < 20, (2 * v1 + v0 / 2 ^ 63) / 2 ^ (3 * (j + 1)) % 8 = 2 * v1 / 2 ^ (3 * (j + 1)) % 2 ^ 3 :=
      fun j _ => dig_carry _ _ _ (by omega) hc (by omega)
    rw [s1, s2, sum_congr_range _ _ 20 hj]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    rw [dig_carry0 _ _ (by omega) hc]
    norm_num
    omega
  rw [e1]
  omega
def lowSum (V : Nat) : Nat := lowSwar (V % 2 ^ 64) (2 * (V / 2 ^ 64))
theorem lowSum_lt (V : Nat) : lowSum V < 4095 := Nat.mod_lt _ (by norm_num)
theorem lowSum_eq (V : Nat) (h : V / 2 ^ 64 < 2 ^ 62) :
    lowSum V = ((List.range 42).map fun i => V / 2 ^ (3 * i) % 2 ^ 3).sum := by
  unfold lowSum
  rw [lowSwar_eq _ _ (Nat.mod_lt _ (by norm_num)) (by omega)]
  have hV : V = V % 2 ^ 64 + 2 ^ 64 * (V / 2 ^ 64) := (Nat.mod_add_div V (2 ^ 64)).symm
  have := lowDigits_sum (V % 2 ^ 64) (V / 2 ^ 64) (Nat.mod_lt _ (by norm_num))
  rw [← hV] at this
  exact this.symm
theorem target_le (lay : Layer) : target lay ≤ 200 := by
  fin_cases lay <;> decide
def lowSumS1 (v : Digest) : Nat := lowSwar (v.toNat % 2 ^ 63) (v.toNat / 2 ^ 64 % 2 ^ 63)
theorem lowSumS1_lt (v : Digest) : lowSumS1 v < 4095 := Nat.mod_lt _ (by norm_num)
theorem lowerWord_eq (v : Digest) :
    lowerWord v = v.toNat % 2 ^ 63 + 2 ^ 63 * (v.toNat / 2 ^ 64 % 2 ^ 63) := by
  unfold lowerWord; ring
theorem lowerWord_digits_sum (A B : Nat) (hA : A < 2 ^ 63) :
    ((List.range 42).map fun i => (A + 2 ^ 63 * B) / 2 ^ (3 * i) % 8).sum = dsum21 A + dsum21 B := by
  rw [show 42 = 21 + 21 from rfl, sum_range_add, dsum21_pow, dsum21_pow]
  have hlow : ∀ i < 21, (A + 2 ^ 63 * B) / 2 ^ (3 * i) % 8 = A / 2 ^ (3 * i) % 2 ^ 3 := by
    intro i hi
    have := div_mod_add_pow A B (3 * i) 63 3 (by omega)
    simpa using this
  rw [sum_congr_range _ _ 21 hlow]
  have hhi : ∀ j < 21, (A + 2 ^ 63 * B) / 2 ^ (3 * (21 + j)) % 8 = B / 2 ^ (3 * j) % 2 ^ 3 := by
    intro j _
    rw [show 3 * (21 + j) = 63 + 3 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
      div_add_pow _ _ _ _ (le_refl _), Nat.div_eq_of_lt hA]
    simp
  rw [sum_congr_range _ _ 21 hhi]
theorem lowSumS1_eq (v : Digest) :
    lowSumS1 v = ((List.range 42).map fun i => lowerWord v / 2 ^ (3 * i) % 8).sum := by
  unfold lowSumS1
  have hA : v.toNat % 2 ^ 63 < 2 ^ 63 := Nat.mod_lt _ (by norm_num)
  rw [lowSwar_eq _ _ (by omega) (Nat.mod_lt _ (by norm_num)), lowerWord_eq,
    lowerWord_digits_sum _ _ hA, Nat.div_eq_of_lt hA, Nat.add_zero]
theorem decode_lower_v6 (lay : Layer) (hlay : lay ≠ 0) (value : Digest) :
    decode lay value =
      if lowerSpare value then
        (if (target lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64 < 8 then
          some (((List.range 42).map fun i => lowerWord value / 2 ^ (3 * i) % 8) ++
            [(target lay + 2 ^ 64 - lowSumS1 value) % 2 ^ 64])
        else none)
      else none := by
  have ht := target_le lay
  have hS := lowSumS1_lt value
  rw [ClaudeWCT.WCT9.decode_lower_eq hlay value]
  by_cases hs : lowerSpare value
  · rw [if_pos hs, if_pos hs]
    unfold ClaudeWCT.WCT9.decodeV5Lower
    rw [if_neg (by have := lowerWord_lt value; omega)]
    dsimp only
    rw [← lowSumS1_eq]
    by_cases hc : lowSumS1 value ≤ target lay ∧ target lay - lowSumS1 value < 8
    · rw [if_pos hc, if_pos (by omega)]
      congr 3
      omega
    · rw [if_neg hc, if_neg (by omega)]
  · rw [if_neg hs, if_neg hs]
end SigGolfCandidate.T3M
end
