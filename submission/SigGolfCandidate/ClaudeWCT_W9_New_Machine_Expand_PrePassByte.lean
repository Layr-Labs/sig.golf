import SigGolfCandidate.ClaudeWCT_W9_New_Machine_Expand_PrePass
import SigGolfCandidate.ClaudeWCT_W9_T3M_SigCodec48
set_option Elab.async false

/-! # The byte theorem of the img-v6 pre-pass

If the 5,239-byte v6 signature `b` is at `0x7000`, then after the pre-pass the 656 dwords at `0x7000` are the
5,248-byte old-codec bytes `SharedCodec48.sigBC (SharedCodec.sigDecC b)` (the form `H2Front` consumes). -/

namespace ClaudeWCT.W9.Machine.Expand.PrePass
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 50000

theorem dv (x a b c : Nat) (h : c ≤ b) : x / 2 ^ a % 2 ^ b / 2 ^ c = x / 2 ^ (a + c) % 2 ^ (b - c) := by
  rw [show 2 ^ b = 2 ^ c * 2 ^ (b - c) by rw [← Nat.pow_add]; congr 1; omega, Nat.mod_mul_right_div_self,
    Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem dm (x a b c d : Nat) (h : c + d ≤ b) : x / 2 ^ a % 2 ^ b / 2 ^ c % 2 ^ d = x / 2 ^ (a + c) % 2 ^ d := by
  rw [dv x a b c (by omega), Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem ofNat_ne (x c : Nat) (hx : x < 2 ^ 64) (hc : c < 2 ^ 64) (h : x ≠ c) :
    ¬ (BitVec.ofNat 64 x = BitVec.ofNat 64 c) := by
  intro e
  apply h
  have := congrArg BitVec.toNat e
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hc] at this

theorem cDigV_toNat (b : SharedCodec.CBytes) (k : Nat) :
    (SharedCodec.cDig b k).toNat = b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  rw [SharedCodec.cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- The old-codec bytes of the decoded v6 signature. -/
abbrev b48 (b : SharedCodec.CBytes) : SharedCodec48.CBytes := SharedCodec48.sigBC (SharedCodec.sigDecC b)

theorem b48_dig (b : SharedCodec.CBytes) (k : Nat) (hk : k < 327) :
    (b48 b).toNat / 2 ^ (128 * k) % 2 ^ 128 =
      if 169 ≤ k ∧ k ≤ 178 then b.toNat / 2 ^ (128 * k) % 2 ^ 128 % 2 ^ (128 - (k - 168))
      else b.toNat / 2 ^ (128 * k) % 2 ^ 128 := by
  have h2 := congrArg BitVec.toNat (SharedCodec48.cDig_sigBC (SharedCodec.sigDecC b) k hk)
  rw [SharedCodec48.cDig, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at h2
  rw [b48, h2, ClaudeWCT.W9.T3M.getD_eraseIdx]
  by_cases h179 : k < 179
  · rw [if_pos h179, SharedCodec.sigDigests_sigDecC b k (by omega)]
    unfold SharedCodec.digC
    rw [if_pos h179]
    by_cases hp : 169 ≤ k ∧ k ≤ 178
    · rw [if_pos hp.1, if_pos hp]
      unfold SharedCodec.clearTop
      have hlt : (SharedCodec.cDig b k).toNat % 2 ^ (128 - (k - 168)) < 2 ^ 128 :=
        lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (Nat.pow_le_pow_right (by decide) (by omega))
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, cDigV_toNat]
    · rw [if_neg hp, if_neg (by omega), cDigV_toNat]
  · rw [if_neg h179, SharedCodec.sigDigests_sigDecC b (k + 1) (by omega), if_neg (by omega)]
    unfold SharedCodec.digC
    rw [if_neg (by omega), if_neg (by omega), cDigV_toNat, Nat.add_sub_cancel]

theorem b48_tail (b : SharedCodec.CBytes) :
    (b48 b).toNat / 2 ^ (128 * 327) =
      (b.toNat / 2 ^ (128 * 327) % 2 ^ 56 + SharedCodec.xOfB b % 2 ^ 42 * 2 ^ 56) +
        2 ^ 112 * (SharedCodec.xOfB b / 2 ^ 42) := by
  have hN := SharedCodec48.sigBC_toNat (SharedCodec.sigDecC b)
  have hD := SigGolfCandidate.T3M.digNat_lt ((SharedCodec.sigDigests (SharedCodec.sigDecC b)).eraseIdx 179)
  rw [SharedCodec.length_eraseIdx_sig] at hD
  rw [b48, hN, show 2 ^ (8 * 5246) = 2 ^ (128 * 327) * 2 ^ 112 by rw [← Nat.pow_add], Nat.mul_assoc,
    Nat.add_assoc, ← Nat.mul_add, ClaudeWCT.W9.T3M.split_div _ _ _ hD, SharedCodec.sigDigests_sigDecC b 179 (by decide)]
  have hx := SharedCodec.xOfB_lt b
  change (SharedCodec.digC b 179).toNat % 2 ^ 112 +
    2 ^ 112 * (BitVec.ofNat 16 (SharedCodec.xOfB b / 2 ^ 42)).toNat = _
  rw [SharedCodec.digC, if_neg (by decide), if_pos rfl, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  generalize SharedCodec.xOfB b = X at *
  generalize b.toNat / 2 ^ (128 * 327) = bt
  omega

/-- The machine's 55-bit field is the codec's `xOfB`. -/
theorem xN_eq (b : SharedCodec.CBytes) (M : Word → Word)
    (hW : ∀ m, 1 ≤ m → m ≤ 10 → (M (BitVec.ofNat 64 (pA m))).toNat = b.toNat / 2 ^ (64 * (337 + 2 * m)) % 2 ^ 64) :
    xN M = SharedCodec.xOfB b := by
  have key : ∀ m, 1 ≤ m → m ≤ 10 → (M (BitVec.ofNat 64 (pA m))).toNat / 2 ^ (64 - m) =
      SharedCodec.topBits m (SharedCodec.cDig b (168 + m)) := by
    intro m h1 h2
    rw [hW m h1 h2, SharedCodec.topBits, cDigV_toNat, dv _ _ _ _ (by omega), dv _ _ _ _ (by omega),
      show 64 * (337 + 2 * m) + (64 - m) = 128 * (168 + m) + (128 - m) by omega,
      show 64 - (64 - m) = 128 - (128 - m) by omega]
  have k1 : (M (BitVec.ofNat 64 (pA 1))).toNat / 2 ^ 63 = SharedCodec.topBits 1 (SharedCodec.cDig b 169) :=
    key 1 (by omega) (by omega)
  have k2 : (M (BitVec.ofNat 64 (pA 2))).toNat / 2 ^ 62 = SharedCodec.topBits 2 (SharedCodec.cDig b 170) :=
    key 2 (by omega) (by omega)
  have k3 : (M (BitVec.ofNat 64 (pA 3))).toNat / 2 ^ 61 = SharedCodec.topBits 3 (SharedCodec.cDig b 171) :=
    key 3 (by omega) (by omega)
  have k4 : (M (BitVec.ofNat 64 (pA 4))).toNat / 2 ^ 60 = SharedCodec.topBits 4 (SharedCodec.cDig b 172) :=
    key 4 (by omega) (by omega)
  have k5 : (M (BitVec.ofNat 64 (pA 5))).toNat / 2 ^ 59 = SharedCodec.topBits 5 (SharedCodec.cDig b 173) :=
    key 5 (by omega) (by omega)
  have k6 : (M (BitVec.ofNat 64 (pA 6))).toNat / 2 ^ 58 = SharedCodec.topBits 6 (SharedCodec.cDig b 174) :=
    key 6 (by omega) (by omega)
  have k7 : (M (BitVec.ofNat 64 (pA 7))).toNat / 2 ^ 57 = SharedCodec.topBits 7 (SharedCodec.cDig b 175) :=
    key 7 (by omega) (by omega)
  have k8 : (M (BitVec.ofNat 64 (pA 8))).toNat / 2 ^ 56 = SharedCodec.topBits 8 (SharedCodec.cDig b 176) :=
    key 8 (by omega) (by omega)
  have k9 : (M (BitVec.ofNat 64 (pA 9))).toNat / 2 ^ 55 = SharedCodec.topBits 9 (SharedCodec.cDig b 177) :=
    key 9 (by omega) (by omega)
  have k10 : (M (BitVec.ofNat 64 (pA 10))).toNat / 2 ^ 54 = SharedCodec.topBits 10 (SharedCodec.cDig b 178) :=
    key 10 (by omega) (by omega)
  unfold xN SharedCodec.xOfB
  rw [k1, k2, k3, k4, k5, k6, k7, k8, k9, k10]

theorem path_word (b : SharedCodec.CBytes) (m : Nat) (hm : 1 ≤ m ∧ m ≤ 10) (W : BitVec 64)
    (hW : W.toNat = b.toNat / 2 ^ (64 * (337 + 2 * m)) % 2 ^ 64) :
    (clrW m W).toNat = (b48 b).toNat / 2 ^ (64 * (337 + 2 * m)) % 2 ^ 64 := by
  rw [clrW_toNat m hm, hW, show 64 * (337 + 2 * m) = 128 * (168 + m) + 64 by omega,
    ← dm (b48 b).toNat (128 * (168 + m)) 128 64 64 (by omega), b48_dig b (168 + m) (by omega),
    if_pos (by omega), show 168 + m - 168 = m by omega, ← dm b.toNat (128 * (168 + m)) 128 64 64 (by omega)]
  generalize b.toNat / 2 ^ (128 * (168 + m)) = y
  have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem other_word (b : SharedCodec.CBytes) (j : Nat) (hj : j < 654)
    (hp : ¬ (j = 339 ∨ j = 341 ∨ j = 343 ∨ j = 345 ∨ j = 347 ∨ j = 349 ∨ j = 351 ∨ j = 353 ∨ j = 355 ∨ j = 357)) :
    b.toNat / 2 ^ (64 * j) % 2 ^ 64 = (b48 b).toNat / 2 ^ (64 * j) % 2 ^ 64 := by
  obtain ⟨k, i, hi, rfl⟩ : ∃ k i, i < 2 ∧ j = 2 * k + i := ⟨j / 2, j % 2, by omega, by omega⟩
  rw [show 64 * (2 * k + i) = 128 * k + 64 * i by omega, ← dm b.toNat (128 * k) 128 (64 * i) 64 (by omega),
    ← dm (b48 b).toNat (128 * k) 128 (64 * i) 64 (by omega), b48_dig b k (by omega)]
  split_ifs with hk
  · obtain rfl : i = 0 := by omega
    rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.div_one,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 64 ≤ 128 - (k - 168)))]
  · rfl

theorem preMem_other (M : Word → Word) (A : Nat) (hA : A < 2 ^ 64) (h1 : A ≠ 33912) (h2 : A ≠ 33904)
    (hp : ¬ (A = pA 1 ∨ A = pA 2 ∨ A = pA 3 ∨ A = pA 4 ∨ A = pA 5 ∨ A = pA 6 ∨ A = pA 7 ∨ A = pA 8 ∨ A = pA 9 ∨
      A = pA 10)) :
    preMem M (BitVec.ofNat 64 A) = M (BitVec.ofNat 64 A) := by
  simp only [not_or] at hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := hp
  unfold preMem
  rw [if_neg (ofNat_ne _ _ hA (by decide) h1), if_neg (ofNat_ne _ _ hA (by decide) h2),
    if_neg (ofNat_ne _ _ hA (by decide) p10), if_neg (ofNat_ne _ _ hA (by decide) p9),
    if_neg (ofNat_ne _ _ hA (by decide) p8), if_neg (ofNat_ne _ _ hA (by decide) p7),
    if_neg (ofNat_ne _ _ hA (by decide) p6), if_neg (ofNat_ne _ _ hA (by decide) p5),
    if_neg (ofNat_ne _ _ hA (by decide) p4), if_neg (ofNat_ne _ _ hA (by decide) p3),
    if_neg (ofNat_ne _ _ hA (by decide) p2), if_neg (ofNat_ne _ _ hA (by decide) p1)]

theorem preMem_path (M : Word → Word) (m : Nat) (hm : 1 ≤ m ∧ m ≤ 10) :
    preMem M (BitVec.ofNat 64 (pA m)) = clrW m (M (BitVec.ofNat 64 (pA m))) := by
  have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold preMem; (repeat rw [if_neg (by decide)]); rw [if_pos rfl])

theorem preMem_654 (M : Word → Word) :
    preMem M (BitVec.ofNat 64 33904) = replaceByte (M (BitVec.ofNat 64 33904)) 7 ((xW M).truncate 8) := by
  unfold preMem
  rw [if_neg (by decide), if_pos rfl]

theorem preMem_655 (M : Word → Word) : preMem M (BitVec.ofNat 64 33912) = dW (xW M) := by
  unfold preMem
  rw [if_pos rfl]

/-- The byte theorem: the pre-pass turns the v6 bytes into the old 5,248-byte codec of the decoded signature. -/
theorem pre_bytes (s t : MachineState) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 654 → s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64)
    (htail : (s.getMem (BitVec.ofNat 64 (0x7000 + 8 * 654))).setWidth 56 = b.extractLsb' (64 * 654) 56)
    (hmem : ∀ A, t.getMem A = preMem s.getMem A) :
    ∀ j, j < 656 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) =
      (SharedCodec48.sigBC (SharedCodec.sigDecC b)).extractLsb' (64 * j) 64 := by
  have hW : ∀ j, j < 654 → (s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))).toNat = b.toNat / 2 ^ (64 * j) % 2 ^ 64 := by
    intro j hj
    rw [hsig j hj, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hP : ∀ m, 1 ≤ m → m ≤ 10 →
      (s.getMem (BitVec.ofNat 64 (pA m))).toNat = b.toNat / 2 ^ (64 * (337 + 2 * m)) % 2 ^ 64 := by
    intro m h1 h2
    rw [show pA m = 0x7000 + 8 * (337 + 2 * m) by unfold pA; omega]
    exact hW _ (by omega)
  have hX : (xW s.getMem).toNat = SharedCodec.xOfB b := by rw [xW_toNat, xN_eq b _ hP]
  have hXl := SharedCodec.xOfB_lt b
  have hT : (s.getMem (BitVec.ofNat 64 33904)).toNat % 2 ^ 56 = b.toNat / 2 ^ (128 * 327) % 2 ^ 56 := by
    have h1 := congrArg BitVec.toNat htail
    rw [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow] at h1
    exact h1
  have hB := b48_tail b
  intro j hj
  apply BitVec.eq_of_toNat_eq
  rw [hmem, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  change (preMem s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j))).toNat = (b48 b).toNat / 2 ^ (64 * j) % 2 ^ 64
  by_cases h655 : j = 655
  · subst h655
    rw [show (0x7000 + 8 * 655 : Nat) = 33912 from rfl, preMem_655, dW_toNat _ (by rw [hX]; exact hXl), hX,
      show 64 * 655 = 128 * 327 + 64 by rfl, Nat.pow_add, ← Nat.div_div_eq_div_mul, hB]
    generalize SharedCodec.xOfB b = X at *
    generalize b.toNat / 2 ^ (128 * 327) = bt
    omega
  by_cases h654 : j = 654
  · subst h654
    rw [show (0x7000 + 8 * 654 : Nat) = 33904 from rfl, preMem_654, replaceByte7, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, hX, hT,
      show 64 * 654 = 128 * 327 by rfl, hB]
    generalize SharedCodec.xOfB b = X at *
    generalize b.toNat / 2 ^ (128 * 327) = bt
    omega
  by_cases hp : j = 339 ∨ j = 341 ∨ j = 343 ∨ j = 345 ∨ j = 347 ∨ j = 349 ∨ j = 351 ∨ j = 353 ∨ j = 355 ∨ j = 357
  · have : ∃ m, 1 ≤ m ∧ m ≤ 10 ∧ j = 337 + 2 * m := by
      rcases hp with h | h | h | h | h | h | h | h | h | h <;> exact ⟨(j - 337) / 2, by omega, by omega, by omega⟩
    obtain ⟨m, h1, h2, rfl⟩ := this
    rw [show 0x7000 + 8 * (337 + 2 * m) = pA m by unfold pA; omega, preMem_path _ m ⟨h1, h2⟩]
    exact path_word b m ⟨h1, h2⟩ _ (hP m h1 h2)
  · rw [preMem_other _ _ (by omega) (by omega) (by omega) (by simp only [pA]; omega), hW j (by omega)]
    exact other_word b j (by omega) hp

/-- Pre-pass, signature-level: from the v6 bytes at `0x7000` the 656 dwords at `0x7000` become the old 5,248-byte
codec of the decoded signature; only dwords in `[0x7000 + 2696, 0x7000 + 5248)` change. -/
theorem pre_spec_bytes (s : MachineState) (hpc : s.pc = pcOf 43250) (b : SharedCodec.CBytes)
    (hsig : ∀ j, j < 654 → s.getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) = b.extractLsb' (64 * j) 64)
    (htail : (s.getMem (BitVec.ofNat 64 (0x7000 + 8 * 654))).setWidth 56 = b.extractLsb' (64 * 654) 56) :
    ∃ t, Steps Images.expandImage s 84 84 t ∧ t.pc = pcOf 44096 ∧
      t.getReg .x6 = 0 ∧ t.getReg .x7 = 0 ∧ t.getReg .x28 = 0 ∧ t.getReg .x30 = 0 ∧
      RegsExcept s t [.x6, .x7, .x28, .x30] ∧
      Frame s t (fun A => 0x7000 + 2696 ≤ A ∧ A < 0x7000 + 5248) ∧
      ∀ j, j < 656 → t.getMem (BitVec.ofNat 64 (0x7000 + 8 * j)) =
        (SharedCodec48.sigBC (SharedCodec.sigDecC b)).extractLsb' (64 * j) 64 := by
  obtain ⟨t, st, tp, t6, t7, t28, t30, rt, mt⟩ := pre_spec s hpc
  refine ⟨t, st, tp, t6, t7, t28, t30, rt, ?_, pre_bytes s t b hsig htail mt⟩
  intro A hA hW
  rw [mt, preMem_other _ _ hA (by omega) (by omega) (by simp only [pA]; omega)]

#print axioms pre_bytes
#print axioms pre_spec_bytes
end ClaudeWCT.W9.Machine.Expand.PrePass
