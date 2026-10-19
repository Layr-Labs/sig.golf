import SigGolfCandidate.T3_Proofs
import SigGolfCandidate.SphincsSecurity_Completeness_Uniform
set_option Elab.async false

/-! # Top-node nonce searches under the lazy random oracle (r3-lean-topbytes, img-v6)

The probabilistic core shared by the v6 KEYGEN moment (every top node is a nonce search with a geometric number of
trials) and the v6 EXPAND excess moment (the brute-forced top-sibling field is uniform):

* `Ev secret program cache F` — the expectation of `F` over the lazy-RO run (`roRun`); `Ev_bind`, `Ev_pure`,
  `Ev_publicQuery_fresh`.
* `topTrial`, `topVal`: the oracle input of trial `n` of the node at `heap` and the node value read from an answer;
  `topNodeHashN_eq`, `topNonceSearch_zero_bind`, `topNonceSearch_succ_bind`, `topTrial_injective`.
* `Ev_topNonceSearch_bind` (value-weighted bound, any `F`) and `V_topNonceSearch_bind` (cost moment), for fresh trial
  inputs and a cache invariant `G` preserved by the search's own queries.
-/

namespace ClaudeWCT.W9.T3.TopMoment
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Sampling
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Expectation of `F` over the lazy-RO run of `program` from `cache`. -/
noncomputable def Ev {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache)
    (F : α × RCache → ℝ≥0∞) : ℝ≥0∞ :=
  expectedValue (roRun secret program cache) F

theorem Ev_bind {α β : Type} (secret : BitVec 256) (program : M α) (next : α → M β) (cache : RCache)
    (F : β × RCache → ℝ≥0∞) :
    Ev secret (program >>= next) cache F = Ev secret program cache (fun r => Ev secret (next r.1) r.2 F) := by
  unfold Ev; rw [roRun_bind, expectedValue_bind]

theorem Ev_pure {α : Type} (secret : BitVec 256) (value : α) (cache : RCache) (F : α × RCache → ℝ≥0∞) :
    Ev secret (pure value : M α) cache F = F (value, cache) := by
  unfold Ev; rw [roRun_pure, expectedValue_pure]

theorem Ev_mono {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache) {F F' : α × RCache → ℝ≥0∞}
    (h : ∀ r, F r ≤ F' r) : Ev secret program cache F ≤ Ev secret program cache F' :=
  expectedValue_mono _ h

theorem Ev_le_of_support {α : Type} (secret : BitVec 256) (program : M α) (cache : RCache)
    {F : α × RCache → ℝ≥0∞} {c : ℝ≥0∞} (h : ∀ r ∈ support (roRun secret program cache), F r ≤ c) :
    Ev secret program cache F ≤ c :=
  expectedValue_le_of_support h

theorem Ev_publicQuery_fresh {β : Type} (secret : BitVec 256) (input : HashInput) (cache : RCache)
    (hfresh : cache input = none) (next : HashOutput → M β) (F : β × RCache → ℝ≥0∞) :
    Ev secret (publicQuery input >>= next) cache F =
      expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
        (fun answer => Ev secret (next answer) (cache.cacheQuery input answer) F) := by
  rw [Ev_bind]
  unfold Ev
  rw [roRun_publicQuery]
  exact expectedValue_fresh input cache hfresh (fun r => expectedValue (roRun secret (next r.1) r.2) F)

/-- Oracle input of trial `n` of the top node at `heap`. -/
def topTrial (heap n : Nat) (left right : Digest) : HashInput := pad64 (topNodeInput heap n left right)
/-- The node value read from an answer (the half kept at `heap`). -/
def topVal (heap : Nat) (answer : HashOutput) : Digest := projHalf (nodeHalfHigh 3 0 heap) answer

theorem topNodeHashN_eq (heap n : Nat) (left right : Digest) :
    topNodeHashN heap n left right =
      (publicQuery (topTrial heap n left right) >>= fun answer => pure (topVal heap answer)) := rfl

theorem topNonceSearch_zero_bind {β : Type} (h heap : Nat) (left right : Digest) (n : Nat)
    (next : Nat × Digest → M β) :
    (topNonceSearch h heap left right 0 n >>= next) =
      (publicQuery (topTrial heap n left right) >>= fun answer => next (n, topVal heap answer)) := by
  simp only [topNonceSearch, topNodeHashN_eq, bind_assoc, pure_bind]

theorem topNonceSearch_succ_bind {β : Type} (h heap : Nat) (left right : Digest) (fuel n : Nat)
    (next : Nat × Digest → M β) :
    (topNonceSearch h heap left right (fuel + 1) n >>= next) =
      (publicQuery (topTrial heap n left right) >>= fun answer =>
        if topZeroOk h (topVal heap answer) then next (n, topVal heap answer)
        else (topNonceSearch h heap left right fuel (n + 1) >>= next)) := by
  simp only [topNonceSearch, topNodeHashN_eq, bind_assoc, pure_bind]
  congr 1
  funext answer
  split <;> simp only [pure_bind]

theorem topNodeInput_length (heap n : Nat) (left right : Digest) : (topNodeInput heap n left right).length = 64 := by
  simp [topNodeInput, nonceBytes, SphincsSecurity.bytesLE_length]

theorem topTrial_length (heap n : Nat) (left right : Digest) : (topTrial heap n left right).length = 64 := by
  simp [topTrial, pad64, topNodeInput_length]

theorem topTrial_injective (heap : Nat) (left right : Digest) {k n : Nat} (hk : k < 2 ^ 64) (hn : n < 2 ^ 64)
    (he : topTrial heap k left right = topTrial heap n left right) : k = n := by
  unfold topTrial at he
  have he' : topNodeInput heap k left right = topNodeInput heap n left right := by
    unfold pad64 at he
    rw [topNodeInput_length, topNodeInput_length] at he
    exact List.append_cancel_right he
  unfold topNodeInput at he'
  simp only [List.append_assoc] at he'
  have h1 := List.append_inj he' (by simp [SphincsSecurity.bytesLE_length])
  have h2 := List.append_inj h1.2 (by simp [SphincsSecurity.bytesLE_length])
  have h3 := List.append_inj h2.2 (by simp [nonceBytes, SphincsSecurity.bytesLE_length])
  have h4 := SphincsSecurity.bytesLE_injective h3.1
  have h5 := congrArg BitVec.toNat h4
  simp only [BitVec.toNat_ofNat] at h5
  rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num)),
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hn] at h5
  exact h5

/-- **Value-weighted bound for a top-node nonce search** (any functional `F`). If every continuation after an
accepted trial with value `v` is bounded by `w v`, then a fresh search is bounded by any `b` with
`E_a[ok ? w(val a) : b] ≤ b` and `E_a[w (val a)] ≤ b` (the last trial is kept). -/
theorem Ev_topNonceSearch_bind {β : Type} (secret : BitVec 256) (h heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (F : β × RCache → ℝ≥0∞) (G : RCache → Prop) (w : Digest → ℝ≥0∞) (b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (topTrial heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      Ev secret (next (k, topVal heap answer)) (cache.cacheQuery (topTrial heap k left right) answer) F ≤
        w (topVal heap answer))
    (hstep : expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if topZeroOk h (topVal heap answer) then w (topVal heap answer) else b) ≤ b)
    (htail : expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun answer => w (topVal heap answer)) ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (topTrial heap k left right) = none) →
      Ev secret (topNonceSearch h heap left right fuel n >>= next) cache F ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_zero_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      exact (expectedValue_mono _ fun answer => hnext cache hg n answer).trans htail
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_succ_bind, Ev_publicQuery_fresh _ _ _ (hfresh n le_rfl (by omega))]
      refine le_trans (expectedValue_mono _ fun answer => ?_) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : topTrial heap k left right ≠ topTrial heap n left right := by
          intro he
          have := topTrial_injective heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

/-- **Cost moment of a top-node nonce search**: every trial is one compression (`z` per trial). -/
theorem V_topNonceSearch_bind {β : Type} (secret : BitVec 256) (z : ℝ≥0∞) (h heap : Nat) (left right : Digest)
    (next : Nat × Digest → M β) (G : RCache → Prop) (B b : ℝ≥0∞)
    (hG : ∀ cache, G cache → ∀ k answer, G (cache.cacheQuery (topTrial heap k left right) answer))
    (hnext : ∀ cache, G cache → ∀ k answer,
      V secret z (next (k, topVal heap answer)) (cache.cacheQuery (topTrial heap k left right) answer) ≤ B)
    (hstep : z * expectedValue ($ᵗ HashOutput : ProbComp HashOutput)
      (fun answer => if topZeroOk h (topVal heap answer) then B else b) ≤ b)
    (htail : z * B ≤ b) :
    ∀ fuel n, n + fuel < 2 ^ 64 → ∀ cache, G cache →
      (∀ k, n ≤ k → k ≤ n + fuel → cache (topTrial heap k left right) = none) →
      V secret z (topNonceSearch h heap left right fuel n >>= next) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_zero_bind, V_publicQuery, topTrial_length]
      have hf := expectedValue_fresh (topTrial heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (next (n, topVal heap r.1)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl ?_) htail
      refine (expectedValue_mono _ fun answer => hnext cache hg n answer).trans ?_
      rw [expectedValue_const (by simp)]
  | succ fuel ih =>
      intro n hn cache hg hfresh
      rw [topNonceSearch_succ_bind, V_publicQuery, topTrial_length]
      have hf := expectedValue_fresh (topTrial heap n left right) cache (hfresh n le_rfl (by omega))
        (fun r => V secret z (if topZeroOk h (topVal heap r.1) then next (n, topVal heap r.1)
          else (topNonceSearch h heap left right fuel (n + 1) >>= next)) r.2)
      refine le_trans (le_of_eq (congrArg (fun t => z ^ (64 / 64) * t) hf)) ?_
      simp only [show (64 : Nat) / 64 = 1 by decide, pow_one]
      refine le_trans (mul_le_mul' le_rfl (expectedValue_mono _ fun answer => ?_)) hstep
      split
      · exact hnext cache hg n answer
      · apply ih (n + 1) (by omega) _ (hG cache hg n answer)
        intro k hk1 hk2
        have hne : topTrial heap k left right ≠ topTrial heap n left right := by
          intro he
          have := topTrial_injective heap left right (by omega) (by omega) he
          omega
        exact (QueryCache.cacheQuery_of_ne (cache := cache) answer hne).trans (hfresh k (by omega) (by omega))

section Prob
open Finset
attribute [local instance] Classical.propDecidable

/-- Bit-window count: exactly `2^(n-k)` words of `n` bits have the `k`-bit window at `s` equal to `j`. -/
theorem window_card (n s k j : Nat) (hsk : s + k ≤ n) (hj : j < 2 ^ k) :
    (univ.filter fun x : BitVec n => x.toNat / 2 ^ s % 2 ^ k = j).card = 2 ^ (n - k) := by
  have e1 : ∀ x : BitVec n, (x.toNat / 2 ^ s % 2 ^ k = j) ↔
      (fun y : BitVec (n - s) => (y.extractLsb' 0 k).toNat = j) (x.extractLsb' s (n - s)) := by
    intro x
    simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [Finset.filter_congr (fun x _ => e1 x)]
  rw [SphincsSecurity.Completeness.card_filter_high (n := n) (w := s) (by omega)
    (fun y : BitVec (n - s) => (y.extractLsb' 0 k).toNat = j)]
  have e2 := SphincsSecurity.Completeness.card_filter_low (n := n - s) (w := k) (by omega)
    (fun u : BitVec k => u.toNat = j)
  rw [e2]
  have h1 : (univ.filter fun u : BitVec k => u.toNat = j).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨BitVec.ofNat k j, ?_⟩
    ext u
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hu
      apply BitVec.eq_of_toNat_eq
      rw [hu, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
    · rintro rfl
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  rw [h1, one_mul, ← pow_add]
  congr 1
  omega

theorem two_pow_div_two_pow (n k : Nat) (hk : k ≤ n) :
    ((2 : ℝ≥0∞) ^ (n - k)) / 2 ^ n = ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  have hn : (2 : ℝ≥0∞) ^ n = 2 ^ (n - k) * 2 ^ k := by rw [← pow_add]; congr 1; omega
  rw [hn, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)),
    mul_comm ((2 : ℝ≥0∞) ^ (n - k))⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]

/-- A `k`-bit window of a uniform answer takes each value with probability `2^-k`. -/
theorem prob_window (s k j : Nat) (hsk : s + k ≤ 256) (hj : j < 2 ^ k) :
    Pr[fun a : HashOutput => a.toNat / 2 ^ s % 2 ^ k = j | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [probEvent_uniformSample, window_card 256 s k j hsk hj, Fintype.card_bitVec]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact two_pow_div_two_pow 256 k (by omega)

/-- Offset of the kept half of a top node answer. -/
def topOff (heap : Nat) : Nat := if nodeHalfHigh 3 0 heap then 128 else 0

theorem topVal_toNat (heap : Nat) (a : HashOutput) :
    (topVal heap a).toNat = a.toNat / 2 ^ topOff heap % 2 ^ 128 := by
  unfold topVal topOff projHalf
  cases nodeHalfHigh 3 0 heap <;> simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

/-- Start of the zero window of a height-`h` node value (img-v6, `b_h = h`). -/
def zeroStart (h : Nat) : Nat := if h = 11 then 98 else 128 - h

theorem topZeroBits_eq {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) : topZeroBits h = h := by
  interval_cases h <;> rfl

theorem window_of_half (x s k : Nat) (hsk : s + k ≤ 128) :
    x % 2 ^ 128 / 2 ^ s % 2 ^ k = x / 2 ^ s % 2 ^ k := by
  have h128 : (2 : Nat) ^ 128 = 2 ^ s * 2 ^ (128 - s) := by rw [← pow_add]; congr 1; omega
  rw [h128, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem topZeroOk_iff {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (v : Digest) :
    topZeroOk h v = true ↔ v.toNat / 2 ^ zeroStart h % 2 ^ h = 0 := by
  unfold topZeroOk zeroStart
  by_cases he : h = 11
  · subst he; simp
  · rw [if_neg he, if_neg he, topZeroBits_eq h1 h11]
    have hv := v.isLt
    have hlt : v.toNat / 2 ^ (128 - h) < 2 ^ h := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]
      exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.mod_eq_of_lt hlt]
    simp

/-- The accepted trials of a height-`h` node are a bit window of the answer. -/
theorem topZeroOk_topVal_iff {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (heap : Nat) (a : HashOutput) :
    topZeroOk h (topVal heap a) = true ↔ a.toNat / 2 ^ (topOff heap + zeroStart h) % 2 ^ h = 0 := by
  rw [topZeroOk_iff h1 h11, topVal_toNat, window_of_half _ _ _ (by unfold zeroStart; split <;> omega),
    Nat.div_div_eq_div_mul, ← pow_add]

theorem topOff_add_le (heap : Nat) : topOff heap + 128 ≤ 256 := by
  unfold topOff; split <;> omega

/-- **Acceptance probability** of a top-node trial at height `h`: exactly `2^-h`. -/
theorem prob_topAccept {h : Nat} (h1 : 1 ≤ h) (h11 : h ≤ 11) (heap : Nat) :
    Pr[fun a : HashOutput => topZeroOk h (topVal heap a) = true | ($ᵗ HashOutput : ProbComp HashOutput)] =
      ((2 : ℝ≥0∞) ^ h)⁻¹ := by
  simp only [topZeroOk_topVal_iff h1 h11]
  exact prob_window _ _ _ (by have := topOff_add_le heap; unfold zeroStart; split <;> omega)
    (by positivity)

/-- Expectation of a two-valued function of a uniform answer. -/
theorem expectedValue_uniform_ite (P : HashOutput → Prop) (B b : ℝ≥0∞) :
    expectedValue ($ᵗ HashOutput : ProbComp HashOutput) (fun a => if P a then B else b) =
      Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] * B +
        (1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]) * b := by
  have hc := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) P
  rw [probFailure_uniformSample, tsub_zero] at hc
  have hn : Pr[fun a => ¬P a | ($ᵗ HashOutput : ProbComp HashOutput)] =
      1 - Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)] :=
    ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top (hc ▸ le_add_right le_rfl)) (by
      rw [add_comm]; exact hc)
  have he : (fun a => if P a then B else b) =
      fun a => (if P a then 1 else 0) * B + (if ¬P a then 1 else 0) * b := by
    funext a; by_cases hp : P a <;> simp [hp]
  rw [he, expectedValue_add, expectedValue_mul_const, expectedValue_mul_const, expectedValue_ite_one,
    expectedValue_ite_one, hn]

end Prob

end ClaudeWCT.W9.T3.TopMoment
