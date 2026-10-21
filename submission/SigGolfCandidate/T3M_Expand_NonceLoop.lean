import SigGolfCandidate.T3M_Expand_NonceBlocks

/-!
# img-v6 expand: the top-node nonce search as a bounded refinement (topfold-v6)

`nonce_run`: after the first node hash (answer `a`, trial 0) the routine 1139 .. 43249 + 1140 .. 1142 refines
`trialTail h heap l r (topNonceCap h - 1) 0 (projHalf _ a)`, i.e. the tail of `T3.topNodeAt h heap l r`, with at most
`29 + 22 * (topNonceCap h - 1) + 20` cycles, and leaves the nonce at `0x66700 + 8 (h - 1)`, the leaf at `0x66758`
and the pad `NODE + 32` cleared. `skip_spec`: the other nodes (lower layers, top root) take 8 or 10 cycles.
Template: T3M/Keygen/TopTree.lean (keygen's nonce search).
-/

namespace SigGolfCandidate.T3M.Expand.SharedRecover
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv OracleComp
open SigGolfCandidate.T3M.Expand
open SigGolfCandidate.T3M.Search (NODE NOUT)
open SigGolfCandidate.T3 (Digest topZeroBits topNonceCap topZeroOk nonceBytes topNodeInput topNodeHashN
  topNonceSearch topNodeAt pad64 zero16)
open SphincsSecurity (bytesLE bytesLE_length)
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

/-! ## Arithmetic of the zero test and the node input (copied from Keygen.TopTree) -/
theorem ne_land_mask_eq_zero (n k w : Nat) :
    n &&& ((2 ^ w - 1) * 2 ^ k) = 0 ↔ n / 2 ^ k % 2 ^ w = 0 := by
  have hM : (2 ^ w - 1) * 2 ^ k = (2 ^ w - 1) <<< k := by rw [Nat.shiftLeft_eq]
  rw [hM]
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    have := congrArg (fun y => Nat.testBit y (j + k)) h
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit] at this
    simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit]
    by_cases hj : j < w
    · have e : j + k - k = j := by omega
      simp only [e, hj, decide_true, Bool.and_true, ge_iff_le, Nat.le_add_left] at this
      simp [hj, this]
    · simp [hj]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
    by_cases hik : k ≤ i
    · by_cases hiw : i - k < w
      · have := congrArg (fun y => Nat.testBit y (i - k)) h
        simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.zero_testBit, hiw, decide_true,
          Bool.true_and] at this
        rw [show i - k + k = i by omega] at this
        simp [this]
      · simp [hiw]
    · simp [hik]
theorem ne_hiword_toNat (v : BitVec 128) : (v.extractLsb' 64 64).toNat = v.toNat / 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  apply Nat.mod_eq_of_lt
  omega
theorem ne_zero_test_hi (v : BitVec 128) (b : Nat) (hb : b ≤ 64) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ b - 1) * 2 ^ (64 - b)) = 0#64) ↔
      v.toNat / 2 ^ (128 - b) = 0 := by
  have hlt : (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ 64 := by
    have h1 : 2 ^ b - 1 < 2 ^ b := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
    calc (2 ^ b - 1) * 2 ^ (64 - b) < 2 ^ b * 2 ^ (64 - b) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
      _ = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add,
    show 64 + (64 - b) = 128 - b by omega]
  have hv : v.toNat / 2 ^ (128 - b) < 2 ^ b := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show b + (128 - b) = 128 by omega]
    exact v.isLt
  rw [Nat.mod_eq_of_lt hv]
theorem ne_zero_test_bits98 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 11 - 1) * 2 ^ 34) = 0#64) ↔
      v.toNat / 2 ^ 98 % 2 ^ 11 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- Campaign T51: the top zero bits are `b_h = 0,0,1,1,2,3,4,5,6,7,8` (#938: `b_h = h`; restated). -/
theorem ne_topZeroBits_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    topZeroBits h = SigGolfCandidate.T3.topZeroAlloc.getD h 0 := rfl

/-- The machine's zero test (43225..43227) is `topZeroOk`. -/
theorem ne_zero_test_bits104 (v : BitVec 128) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 ((2 ^ 8 - 1) * 2 ^ 40) = 0#64) ↔
      v.toNat / 2 ^ 104 % 2 ^ 8 = 0 := by
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by norm_num), ne_hiword_toNat,
    BitVec.toNat_zero, ne_land_mask_eq_zero, Nat.div_div_eq_div_mul, ← Nat.pow_add]
/-- The machine's zero test (43225..43227, mask from ZB 54553) is `topZeroOk`. -/
theorem ne_zero_test (v : Digest) (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    (v.extractLsb' 64 64 &&& BitVec.ofNat 64 (maskE h) = 0#64) ↔ topZeroOk h v = true := by
  unfold maskE topZeroOk
  by_cases hc : h = 11
  · rw [if_pos hc, if_pos hc, show (255 : Nat) * 2 ^ 40 = (2 ^ 8 - 1) * 2 ^ 40 by norm_num, ne_zero_test_bits104,
      beq_iff_eq]
  · have hb : topZeroBits h ≤ 64 := by interval_cases h <;> decide
    rw [if_neg hc, if_neg hc, ne_zero_test_hi v _ hb, beq_iff_eq]

theorem ne_nonce_words (n : Nat) (hn : n < 2 ^ 64) : wordsOf (nonceBytes n) = [BitVec.ofNat 64 n, 0] := by
  unfold nonceBytes
  rw [wordsOf_bytesLE16]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  · congr 1
    apply BitVec.eq_of_toNat_eq
    have h0 : n % 2 ^ 64 % 2 ^ 128 / 2 ^ 64 = 0 := by omega
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, h0, Nat.zero_mod]
    rfl
theorem ne_topNodeInput_length (heap n : Nat) (l r : Digest) : (topNodeInput heap n l r).length = 64 := by
  simp [topNodeInput, nonceBytes, bytesLE_length]
theorem ne_wordsOf_topNodeInput (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64) (l r : Digest) :
    wordsOf (topNodeInput heap n l r) =
      [l.extractLsb' 0 64, l.extractLsb' 64 64, BitVec.ofNat 64 heap, 0, BitVec.ofNat 64 n, 0,
        r.extractLsb' 0 64, r.extractLsb' 64 64] := by
  unfold topNodeInput
  rw [wordsOf_append _ _ (by simp [bytesLE_length, nonceBytes]), wordsOf_append _ _ (by simp [bytesLE_length]),
    wordsOf_append _ _ (by simp [bytesLE_length]), wordsOf_bytesLE16, wordsOf_bytesLE16, ne_nonce_words n hn,
    wordsOf_bytesLE16, Keygen.nodeTweak_3_top 0 heap h1 h2, T3.append64_low]
  have hhi : (0#64 ++ BitVec.ofNat 64 (Keygen.nodeLo 0 0 + heap)).extractLsb' 64 64 = 0#64 :=
    BitVec.extractLsb'_append_eq_left
  rw [hhi]
  simp [Keygen.nodeLo]
theorem ne_topNodeInput_blocks (heap n : Nat) (l r : Digest) :
    (toQ (pad64 (topNodeInput heap n l r))).blocks = 1 := by
  rw [pad64_of_aligned _ (by rw [ne_topNodeInput_length]),
    blocks_toQ ⟨by rw [ne_topNodeInput_length]; omega, by rw [ne_topNodeInput_length]⟩, ne_topNodeInput_length]
theorem ne_hashInput_topNode (t : MachineState) (heap n : Nat) (h1 : 1 ≤ heap) (h2 : heap < 4096) (hn : n < 2 ^ 64)
    (l r : Digest) (h10 : t.getReg .x10 = BitVec.ofNat 64 NODE) (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (w0 : t.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64)
    (w8 : t.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64)
    (w16 : t.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap)
    (w24 : t.getMem (BitVec.ofNat 64 (NODE + 24)) = 0)
    (w32 : t.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    (w40 : t.getMem (BitVec.ofNat 64 (NODE + 40)) = 0)
    (w48 : t.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64)
    (w56 : t.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64) :
    hashInput t = toQ (pad64 (topNodeInput heap n l r)) := by
  rw [pad64_of_aligned _ (by rw [ne_topNodeInput_length])]
  refine hashInput_toQ t _ 0 NODE (ne_topNodeInput_length _ _ _ _) h10 (by decide) (by decide) h11 (by decide) ?_
  rw [ne_wordsOf_topNodeInput heap n h1 h2 hn, readWords_eight, w0, w8, w16, w24, w32, w40, w48, w56]
theorem ne_out_after_hash (t : MachineState) (a : BitVec 256) (heap : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 NOUT) :
    DigAt (writeHash t a) (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  rw [T3.nodeHalfHigh_top]
  rcases Nat.mod_two_eq_zero_or_one heap with hp | hp
  · have hd : decide (heap % 2 = 0) = true := by simp [hp]
    rw [hd, T3.projHalf_true, hp, show NOUT + 16 - 16 * 0 = NOUT + 16 from rfl]
    exact DigAt.writeHash_hi t a NOUT h12 (by decide)
  · have hd : decide (heap % 2 = 0) = false := by simp [hp]
    rw [hd, T3.projHalf_false, hp, show NOUT + 16 - 16 * 1 = NOUT from rfl]
    exact DigAt.writeHash_lo t a NOUT h12 (by decide)

/-- What follows the trial-`n` hash in `topNonceSearch` (fuel = trials left). -/
def neTrialTail (h heap : Nat) (l r : Digest) : Nat → Nat → Digest → T3.M (Nat × Digest)
  | 0, n, v => pure (n, v)
  | fuel + 1, n, v => if topZeroOk h v then pure (n, v) else topNonceSearch h heap l r fuel (n + 1)
theorem ne_topNonceSearch_eq (h heap : Nat) (l r : Digest) (fuel n : Nat) :
    topNonceSearch h heap l r fuel n = topNodeHashN heap n l r >>= neTrialTail h heap l r fuel n := by
  cases fuel <;> rfl
theorem ne_topNodeHashN_bind {β : Type} (heap n : Nat) (l r : Digest) (g : Digest → T3.M β) :
    topNodeHashN heap n l r >>= g =
      T3.publicHash (topNodeInput heap n l r) >>= fun a => g (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by
  unfold topNodeHashN T3.projHash; rw [bind_assoc]; simp only [pure_bind]
theorem ne_topNonceCap_le (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) :
    1 ≤ topNonceCap h ∧ topNonceCap h ≤ 104 * 2048 := by
  interval_cases h <;> decide
/-- Campaign T51: the cap is `104 << b_h` (#938: `104 << h`; restated). -/
theorem ne_topNonceCap_eq (h : Nat) (h1 : 1 ≤ h) (h11 : h ≤ 11) : topNonceCap h = 104 * 2 ^ topZeroBits h := rfl

theorem ne_nonceBytes_zero : nonceBytes 0 = zero16 := by decide

section sim
variable {α β : Type} {image : Image} {sk : BitVec 256}
theorem ne_tb_pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : TBSim image sk s c (Pure.pure a) Q :=
  Sim.pure_steps h hQ
theorem ne_tb_publicHash_bind {s : MachineState} {input : List UInt8} {W : Nat}
    {f : T3.HashOutput → T3.M β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = toQ (T3.pad64 input))
    (h : ∀ a, TBSim image sk (writeHash s a) W (f a) Q) :
    TBSim image sk s (8 * (toQ (T3.pad64 input)).blocks + W) (T3.publicHash input >>= f) Q := by
  unfold TBSim; rw [mrealize_bind, mrealize_publicHash]
  exact Sim.query_bind hf ht0 hv hq h
end sim

section run
variable {im : Image} [Code im] {sk : BitVec 256}

/-! ## The skip path (lower layers and the top root) -/
theorem skip_spec (s : MachineState) (hpc : s.pc = pcOf 1139) (hh j P M : Nat) (hh' : hh < 2 ^ 64)
    (hj : j < 2 ^ 63) (hM : 64 ≤ M) (hM' : M < 2 ^ 64) (hskip : hh ≠ 12 ∨ 11 ≤ j)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 hh) (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 P) (h24 : s.getReg .x24 = BitVec.ofNat 64 M) :
    ∃ t k, Steps im s k k t ∧ k ≤ 10 ∧ t.pc = pcOf 1076 ∧ t.getReg .x22 = BitVec.ofNat 64 (P + 16) ∧
      t.getReg .x24 = BitVec.ofNat 64 (M - 64) ∧ t.getReg .x20 = BitVec.ofNat 64 (j + 1) ∧
      RegsExcept s t [.x20, .x22, .x24, .x28] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := n1139_spec (im := im) s hpc
  obtain ⟨t2, s2, p2, r2, f2⟩ := nA_spec (im := im) t1 p1 hh hh' (by rw [r1.get (by simp)]; exact h15)
  have r12 : RegsExcept s t2 [.x28] := (r1.trans r2).mono (by decide)
  obtain ⟨t3, k3, s3, hk3, p3, r3, f3⟩ : ∃ t3 k3, Steps im t2 k3 k3 t3 ∧ k3 ≤ 2 ∧ t3.pc = pcOf 43248 ∧
      RegsExcept t2 t3 [.x28] ∧ Frame t2 t3 (fun _ => False) := by
    by_cases hc : hh = 12
    · rw [if_pos hc] at p2
      obtain ⟨t3, s3, p3, r3, f3⟩ := nB_spec (im := im) t2 p2 j (by omega) (by rw [r12.get (by simp)]; exact h20)
      rw [if_pos (by omega)] at p3
      exact ⟨t3, 2, s3, le_rfl, p3, r3, f3⟩
    · rw [if_neg hc] at p2
      exact ⟨t2, 0, Steps.refl _, by omega, p2, RegsExcept.refl _ _, Frame.refl _ _⟩
  have r13 : RegsExcept s t3 [.x28] := (r12.trans r3).mono (by decide)
  obtain ⟨t4, s4, p4, x22, r4, f4⟩ := nS_spec (im := im) t3 p3 P (by rw [r13.get (by simp)]; exact h22)
  obtain ⟨t5, s5, p5, x24, x20, r5, f5⟩ := n1140_spec (im := im) t4 p4 M j hM hM'
    (by rw [r4.get (by simp), r13.get (by simp)]; exact h24) (by rw [r4.get (by simp), r13.get (by simp)]; exact h20)
  refine ⟨t5, 1 + 2 + k3 + 2 + 3, (((s1.trans s2).trans s3).trans s4).trans s5, by omega, p5,
    by rw [r5.get (by simp)]; exact x22, x24, x20, ?_, ?_⟩
  · exact ((r13.trans r4).trans r5).mono (by decide)
  · exact ((((f1.trans f2).trans f3).trans f4).trans f5).mono (fun _ _ h => by simp_all)

/-! ## The nonce path -/
/-- Cycles of the setup 1139 .. 43224 at height `h` (T51: 43199/43200 `j 54553`, ZB 54553..54568, `j 43215`). -/
def nsetupK (h : Nat) : Nat := 17 + zbK h
theorem nsetupK_le (h : Nat) : nsetupK h ≤ 32 := by unfold nsetupK zbK; split_ifs <;> omega
theorem nsetup_spec (s : MachineState) (hpc : s.pc = pcOf 1139) (j leaf : Nat) (hj : j < 11) (hl : leaf < 2 ^ 64)
    (h15 : s.getReg .x15 = BitVec.ofNat 64 12) (h20 : s.getReg .x20 = BitVec.ofNat 64 j)
    (h18 : s.getReg .x18 = BitVec.ofNat 64 leaf) :
    ∃ t, Steps im s (nsetupK (j + 1)) (nsetupK (j + 1)) t ∧ t.pc = pcOf 43225 ∧
      t.getReg .x31 = BitVec.ofNat 64 (maskE (j + 1)) ∧ t.getReg .x17 = BitVec.ofNat 64 (topNonceCap (j + 1)) ∧
      t.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (leaf / 2 ^ (j + 1) % 2)) ∧
      RegsExcept s t [.x13, .x14, .x17, .x28, .x29, .x30, .x31] ∧ Frame s t (fun _ => False) := by
  obtain ⟨t1, s1, p1, r1, f1⟩ := n1139_spec (im := im) s hpc
  obtain ⟨t2, s2, p2, r2, f2⟩ := nA_spec (im := im) t1 p1 12 (by norm_num) (by rw [r1.get (by simp)]; exact h15)
  rw [if_pos rfl] at p2
  have r12 : RegsExcept s t2 [.x28] := (r1.trans r2).mono (by decide)
  obtain ⟨t3, s3, p3, r3, f3⟩ := nB_spec (im := im) t2 p2 j (by omega) (by rw [r12.get (by simp)]; exact h20)
  rw [if_neg (by omega)] at p3
  have r13 : RegsExcept s t3 [.x28] := (r12.trans r3).mono (by decide)
  obtain ⟨t4, s4, p4, x13, r4, f4⟩ := nC_spec (im := im) t3 p3 j (by rw [r13.get (by simp)]; exact h20)
  obtain ⟨t5, s5, p5, x14, x31, r5, f5⟩ := nZ_spec (im := im) t4 p4 (j + 1) (by omega) (by omega) x13
  have hb : topZeroBits (j + 1) ≤ 11 := by interval_cases j <;> decide
  obtain ⟨t8, s8, p8, x17, x29, r8, f8⟩ := nG_spec (im := im) t5 p5 (j + 1) (topZeroBits (j + 1)) leaf (by omega) hb hl
    (by rw [r5.get (by simp)]; exact x13) x14
    (by rw [r5.get (by simp), r4.get (by simp), r13.get (by simp)]; exact h18)
  refine ⟨t8, ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s8)).of_eq
      (by unfold nsetupK; omega) (by unfold nsetupK; omega),
    p8, by rw [r8.get (by simp)]; exact x31, ?_, x29, ?_, ?_⟩
  · rw [x17, ne_topNonceCap_eq _ (by omega) (by omega)]
  · exact (((r13.trans r4).trans r5).trans r8).mono (by decide)
  · exact (((((f1.trans f2).trans f3).trans f4).trans f5).trans f8).mono
      (fun _ _ h => by simp_all)

/-- The state right before the first node hash (at 1138): arguments, node words, climb registers. -/
structure NFacts (t2 : MachineState) (heap leaf j P M : Nat) (l r : Digest) : Prop where
  x5 : t2.getReg .x5 = 0
  x12 : t2.getReg .x12 = BitVec.ofNat 64 NOUT
  x15 : t2.getReg .x15 = BitVec.ofNat 64 12
  x18 : t2.getReg .x18 = BitVec.ofNat 64 leaf
  x20 : t2.getReg .x20 = BitVec.ofNat 64 j
  x22 : t2.getReg .x22 = BitVec.ofNat 64 P
  x24 : t2.getReg .x24 = BitVec.ofNat 64 M
  w0 : t2.getMem (BitVec.ofNat 64 NODE) = l.extractLsb' 0 64
  w8 : t2.getMem (BitVec.ofNat 64 (NODE + 8)) = l.extractLsb' 64 64
  w16 : t2.getMem (BitVec.ofNat 64 (NODE + 16)) = BitVec.ofNat 64 heap
  w24 : t2.getMem (BitVec.ofNat 64 (NODE + 24)) = 0
  w32 : t2.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  w40 : t2.getMem (BitVec.ofNat 64 (NODE + 40)) = 0
  w48 : t2.getMem (BitVec.ofNat 64 (NODE + 48)) = r.extractLsb' 0 64
  w56 : t2.getMem (BitVec.ofNat 64 (NODE + 56)) = r.extractLsb' 64 64
  h1 : 1 ≤ heap
  h2 : heap < 4096
  hj : j < 11
  hpar : leaf / 2 ^ (j + 1) % 2 = heap % 2
  hl : leaf < 2 ^ 64
  hM : 64 ≤ M
  hM' : M < 2 ^ 64

def nTrialRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x17, .x28, .x29, .x30, .x31]
def NTrialW (X : Nat) : Prop := X = NODE + 32 ∨ (NOUT ≤ X ∧ X < NOUT + 32)

/-- At 43225 after the trial-`n` hash (answer `a`). -/
structure NTrialSt (t2 : MachineState) (h heap n : Nat) (a : BitVec 256) (u : MachineState) : Prop where
  pc : u.pc = pcOf 43225
  regs : RegsExcept t2 u nTrialRegs
  x31 : u.getReg .x31 = BitVec.ofNat 64 (maskE h)
  x17 : u.getReg .x17 = BitVec.ofNat 64 (topNonceCap h)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (NOUT + 16 - 16 * (heap % 2))
  pad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n
  frame : Frame t2 u NTrialW
  out : DigAt u (NOUT + 16 - 16 * (heap % 2)) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)

def nExitRegs : List Reg := [.x10, .x11, .x12, .x13, .x14, .x17, .x20, .x22, .x24, .x28, .x29, .x30, .x31]
def NExitW (j : Nat) (X : Nat) : Prop := (NOUT ≤ X ∧ X < NOUT + 32) ∨ X = 0x66758 ∨ X = 0x66700 + 8 * j

/-- Back at 1076 with the node value kept, the nonce recorded and the pad cleared. -/
structure NPost (t2 : MachineState) (heap leaf j P M : Nat) (res : Nat × Digest) (w : MachineState) : Prop where
  pc : w.pc = pcOf 1076
  x20 : w.getReg .x20 = BitVec.ofNat 64 (j + 1)
  x22 : w.getReg .x22 = BitVec.ofNat 64 (P + 16)
  x24 : w.getReg .x24 = BitVec.ofNat 64 (M - 64)
  pad : w.getMem (BitVec.ofNat 64 (NODE + 32)) = 0
  leafAt : w.getMem (BitVec.ofNat 64 0x66758) = BitVec.ofNat 64 leaf
  nonceAt : w.getMem (BitVec.ofNat 64 (0x66700 + 8 * j)) = BitVec.ofNat 64 res.1
  out : DigAt w (NOUT + 16 - 16 * (heap % 2)) res.2
  regs : RegsExcept t2 w nExitRegs
  frame : Frame t2 w (NExitW j)

theorem n_exit {t2 u : MachineState} {heap leaf j P M : Nat} {l r : Digest} (F : NFacts t2 heap leaf j P M l r)
    (hpc : u.pc = pcOf 43240) {L : List Reg} (hL : ∀ x ∈ L, x ∈ nTrialRegs) (hr : RegsExcept t2 u L)
    (hf : Frame t2 u NTrialW) {n : Nat} (hpad : u.getMem (BitVec.ofNat 64 (NODE + 32)) = BitVec.ofNat 64 n)
    {v : Digest} (hv : DigAt u (NOUT + 16 - 16 * (heap % 2)) v) :
    ∃ w, Steps im u 13 13 w ∧ NPost t2 heap leaf j P M (n, v) w := by
  have g : ∀ x, x ∉ nTrialRegs → u.getReg x = t2.getReg x := fun x hx => hr.get (fun hm => hx (hL x hm))
  have hj := F.hj
  obtain ⟨u1, s1, p1, m32, m58, mj, r1, f1⟩ := nK_spec (im := im) u hpc j hj
    (by rw [g _ (by simp [nTrialRegs])]; exact F.x20)
  obtain ⟨u2, s2, p2, x22, r2, f2⟩ := nS_spec (im := im) u1 p1 P
    (by rw [r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x22)
  obtain ⟨w, s3, p3, x24, x20, r3, f3⟩ := n1140_spec (im := im) u2 p2 M j F.hM F.hM'
    (by rw [r2.get (by simp), r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x24)
    (by rw [r2.get (by simp), r1.get (by simp), g _ (by simp [nTrialRegs])]; exact F.x20)
  have f23 : Frame u1 w (fun _ => False) := (f2.trans f3).mono (fun _ _ h => by simp_all)
  have hpar := F.hpar
  have hoff : NOUT + 16 - 16 * (heap % 2) + 16 ≤ NOUT + 32 := by simp only [NOUT]; omega
  refine ⟨w, (s1.trans s2).trans s3, ⟨p3, x20, by rw [r3.get (by simp)]; exact x22, x24, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [f23.get (by decide) (fun h => h), m32]
  · rw [f23.get (by decide) (fun h => h), m58, g _ (by simp [nTrialRegs]), F.x18]
  · rw [f23.get (by omega) (fun h => h), mj, hpad]
  · refine (hv.frame f1 (by simp only [NOUT]; omega) ?_ ?_).frame f23 (by simp only [NOUT]; omega)
      (fun h => h) (fun h => h)
    all_goals (simp only [NOUT, NODE]; omega)
  · exact (((hr.mono hL).trans r1).trans (r2.trans r3)).mono (by decide)
  · intro A hA hn
    unfold NExitW at hn
    by_cases h32 : A = NODE + 32
    · subst h32
      rw [f23.get (by decide) (fun h => h), m32, F.w32]
    · rw [f23.get hA (fun h => h), f1.get hA (by simp only [NODE] at h32 ⊢; omega),
        hf.get hA (by unfold NTrialW; simp only [NODE, NOUT] at h32 hn ⊢; omega)]

section loop
variable (sk) {t2 : MachineState} {heap leaf j P M : Nat} {l r : Digest} (F : NFacts t2 heap leaf j P M l r)
include F

theorem n_check {n : Nat} {a : BitVec 256} {u : MachineState} (hu : NTrialSt t2 (j + 1) heap n a u) :
    ∃ u1, Steps im u 3 3 u1 ∧
      u1.pc = (if topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true then pcOf 43240
        else pcOf 43228) ∧
      RegsExcept u u1 [.x30] ∧ Frame u u1 (fun _ => False) := by
  have hj := F.hj
  have hX : NOUT + 16 - 16 * (heap % 2) = NOUT ∨ NOUT + 16 - 16 * (heap % 2) = NOUT + 16 := by
    rcases Nat.mod_two_eq_zero_or_one heap with h | h <;> rw [h] <;> simp
  obtain ⟨u1, s1, p1, r1, f1⟩ := nL_spec (im := im) u hu.pc _ hX hu.x29
  refine ⟨u1, s1, ?_, r1, f1⟩
  rw [p1, hu.x31, hu.out.2]
  by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
  · rw [if_pos ((ne_zero_test _ (j + 1) (by omega) (by omega)).mpr hz), if_pos hz]
  · rw [if_neg (fun hc => hz ((ne_zero_test _ (j + 1) (by omega) (by omega)).mp hc)), if_neg hz]

theorem n_trial_loop : ∀ fuel n (a : BitVec 256) u, NTrialSt t2 (j + 1) heap n a u →
    n + fuel + 1 = topNonceCap (j + 1) →
    TBSim im sk u (22 * fuel + 20)
      (neTrialTail (j + 1) heap l r fuel n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => NPost t2 heap leaf j P M res w) := by
  have hj := F.hj
  have hcap := ne_topNonceCap_le (j + 1) (by omega) (by omega)
  intro fuel
  induction fuel with
  | zero =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := n_check (im := im) F hu
    by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p1 (L := nTrialRegs ++ [.x30]) (by simp [nTrialRegs])
        (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, -, -, r2, f2⟩ := nH_spec (im := im) u1 p1 n (topNonceCap (j + 1)) (by omega) (by omega)
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad) (by rw [r1.get (by simp)]; exact hu.x17)
      rw [if_pos (by omega)] at p2
      have f12 : Frame u u2 (fun _ => False) := (f1.trans f2).mono (fun X _ h => by simp_all)
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p2 (L := nTrialRegs ++ [.x30] ++ [.x28, .x30])
        (by simp [nTrialRegs]) ((hu.regs.trans r1).trans r2)
        ((hu.frame.trans f12).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f12.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f12 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans (s2.trans sw)) hw).mono (by omega)
        (fun _ _ h => h)
  | succ fuel ih =>
    intro n a u hu hn
    obtain ⟨u1, s1, p1, r1, f1⟩ := n_check (im := im) F hu
    by_cases hz : topZeroOk (j + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) = true
    · rw [if_pos hz] at p1
      obtain ⟨w, sw, hw⟩ := n_exit (im := im) F p1 (L := nTrialRegs ++ [.x30]) (by simp [nTrialRegs])
        (hu.regs.trans r1)
        ((hu.frame.trans f1).mono (fun X _ h => by rcases h with h | h; exact h; exact h.elim))
        (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad)
        (hu.out.frame f1 (by simp only [NOUT]; omega) (fun h => h) (fun h => h))
      have e : neTrialTail (j + 1) heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          pure (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) := by simp only [neTrialTail, hz, if_true]
      rw [e]
      exact (ne_tb_pure_steps (sk := sk) (Q := fun res w => NPost t2 heap leaf j P M res w)
        (a := (n, T3.projHalf (T3.nodeHalfHigh 3 0 heap) a)) (s1.trans sw) hw).mono (by omega) (fun _ _ h => h)
    · rw [if_neg hz] at p1
      obtain ⟨u2, s2, p2, x28_2, x30_2, r2, f2⟩ := nH_spec (im := im) u1 p1 n (topNonceCap (j + 1)) (by omega)
        (by omega) (by rw [f1.get (by decide) (fun h => h)]; exact hu.pad) (by rw [r1.get (by simp)]; exact hu.x17)
      rw [if_neg (by omega)] at p2
      obtain ⟨u3, s3, p3, m32_3, x10_3, x11_3, x12_3, r3, f3⟩ := nI_spec (im := im) u2 p2 x28_2
      have r03 : RegsExcept t2 u3 (nTrialRegs ++ [.x30] ++ [.x28, .x30] ++ [.x10, .x11, .x12]) :=
        ((hu.regs.trans r1).trans r2).trans r3
      have g3 : ∀ x, x ∉ nTrialRegs → u3.getReg x = t2.getReg x := fun x hx => r03.get (fun hm => hx
        ((by decide : ∀ y ∈ nTrialRegs ++ [Reg.x30] ++ [.x28, .x30] ++ [.x10, .x11, .x12], y ∈ nTrialRegs) x hm))
      have f03 : Frame t2 u3 NTrialW := (((hu.frame.trans f1).trans f2).trans f3).mono (fun X _ h => by
        rcases h with ((h | h) | h) | h
        · exact h
        · exact h.elim
        · exact h.elim
        · exact Or.inl h)
      have fr : ∀ X, X < 2 ^ 64 → ¬ NTrialW X → u3.getMem (BitVec.ofNat 64 X) = t2.getMem (BitVec.ofNat 64 X) :=
        fun X hX hn => f03.get hX hn
      have nW : ∀ X, X < NODE + 32 ∨ (NODE + 32 < X ∧ X < NOUT) → ¬ NTrialW X := by
        intro X hX hw; unfold NTrialW at hw; simp only [NODE, NOUT] at hX hw; omega
      have hq : hashInput u3 = toQ (pad64 (topNodeInput heap (n + 1) l r)) :=
        ne_hashInput_topNode u3 heap (n + 1) F.h1 F.h2 (by omega) l r x10_3 x11_3
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w0])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w8])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w16])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE]; omega)), F.w24])
          (by rw [m32_3, x30_2])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w40])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w48])
          (by rw [fr _ (by decide) (nW _ (by simp only [NODE, NOUT]; omega)), F.w56])
      have hv : hashArgumentsValid u3 = true :=
        hashArgs_const u3 NODE 64 NOUT x10_3 x11_3 x12_3 (by decide) (by decide) (by decide) (by decide) (by decide)
      have h5 : u3.getReg .x5 = 0 := by rw [g3 _ (by simp [nTrialRegs]), F.x5]
      have e : neTrialTail (j + 1) heap l r (fuel + 1) n (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a) =
          T3.publicHash (topNodeInput heap (n + 1) l r) >>= fun a' =>
            neTrialTail (j + 1) heap l r fuel (n + 1) (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a') := by
        rw [neTrialTail.eq_2, if_neg hz, ne_topNonceSearch_eq, ne_topNodeHashN_bind]
      rw [e]
      refine (TBSim.steps (s1.trans (s2.trans s3)) (ne_tb_publicHash_bind (fetch_n43238 (im := im) u3 p3) h5 hv hq
        (W := 1 + (22 * fuel + 20)) (fun a' => ?_))).mono (by rw [ne_topNodeInput_blocks] <;> omega)
        (fun _ _ h => h)
      have hwf := Frame.writeHash u3 a' NOUT x12_3 (by decide)
      obtain ⟨w, s4, p4, r4, f4⟩ := nJ_spec (im := im) (writeHash u3 a') (by rw [pc_writeHash, p3, pcOf_add4])
      refine TBSim.steps s4 (ih (n + 1) a' w ⟨p4, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ (by omega))
      · have hw0 : RegsExcept u3 (writeHash u3 a') [] := fun r _ => getReg_writeHash u3 a' r
        exact ((r03.trans hw0).trans r4).mono (by decide)
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x31]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x17]
      · rw [r4.get (by simp), getReg_writeHash, r3.get (by simp), r2.get (by simp), r1.get (by simp), hu.x29]
      · rw [f4.get (by decide) (fun h => h), hwf.get (by decide) (by simp only [NODE, NOUT]; omega), m32_3, x30_2]
      · exact ((f03.trans hwf).trans f4).mono (fun X _ h => by
          rcases h with (h | h) | h
          · exact h
          · exact Or.inr h
          · exact h.elim)
      · exact (ne_out_after_hash u3 a' heap x12_3).frame f4 (by simp only [NOUT]; omega) (fun h => h) (fun h => h)

/-- The nonce routine after the trial-0 node hash (answer `a`), up to 1076. -/
theorem nonce_run (hpc : t2.pc = pcOf 1138) (a : BitVec 256) :
    TBSim im sk (writeHash t2 a) (32 + (22 * (topNonceCap (j + 1) - 1) + 20))
      (neTrialTail (j + 1) heap l r (topNonceCap (j + 1) - 1) 0 (T3.projHalf (T3.nodeHalfHigh 3 0 heap) a))
      (fun res w => NPost t2 heap leaf j P M res w) := by
  have hj := F.hj
  have hcap := ne_topNonceCap_le (j + 1) (by omega) (by omega)
  have p0 : (writeHash t2 a).pc = pcOf 1139 := by rw [pc_writeHash, hpc, pcOf_add4]
  have hw0 : RegsExcept t2 (writeHash t2 a) [] := fun r _ => getReg_writeHash t2 a r
  have fw := Frame.writeHash t2 a NOUT F.x12 (by decide)
  obtain ⟨u, su, pu, x31, x17, x29, ru, fu⟩ := nsetup_spec (im := im) (writeHash t2 a) p0 j leaf hj F.hl
    (by rw [getReg_writeHash]; exact F.x15) (by rw [getReg_writeHash]; exact F.x20)
    (by rw [getReg_writeHash]; exact F.x18)
  have hst : NTrialSt t2 (j + 1) heap 0 a u := by
    refine ⟨pu, (hw0.trans ru).mono (by decide), x31, x17, by rw [x29, F.hpar], ?_, ?_, ?_⟩
    · rw [fu.get (by decide) (fun h => h), fw.get (by decide) (by simp only [NODE, NOUT]; omega), F.w32] <;> rfl
    · exact (fw.trans fu).mono (fun X _ h => by
        rcases h with h | h
        · exact Or.inr h
        · exact h.elim)
    · exact (ne_out_after_hash t2 a heap F.x12).frame fu (by simp only [NOUT]; omega) (fun h => h) (fun h => h)
  refine (TBSim.steps su (n_trial_loop sk F (topNonceCap (j + 1) - 1) 0 a u hst (by omega))).mono
    (by have := nsetupK_le (j + 1); omega) (fun _ _ h => h)

end loop
end run
end SigGolfCandidate.T3M.Expand.SharedRecover
