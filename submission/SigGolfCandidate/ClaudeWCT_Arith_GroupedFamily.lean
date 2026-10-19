import SigGolfCandidate.ClaudeWCT_Arith_FamilyTest
import SigGolfCandidate.Research_V7Composed198Closing

/-!
# Lower seed families of `g` leaves: generic-`g` side channel, charge and live closing (r3-lean-seedfam)

* `GroupedFamily.family_test_le_grouped`: the family side channel (`family_test_le`) for a family of `g ≤ 23`
  lower leaves: chains `Fin g × Fin 43`, points `l·43 + c + 1 < 1024`, `n = 5g + 3` coefficients, at most `5g`
  revealed seeds. With the one-sided constant (`kconst D = D²`, `comp_mass_le`) the per-chain error is
  `2 δ³ q² · E[#tests of the family]`.
* `GroupedFamily.sum_charge_le`: every test is a test of at most one family, which has at most `C` chains, so the
  per-chain counts sum to at most `C · #tests` (the generic form of `sum_NL_le`).
* `GroupedFamily.seed_charge_real`: `errConst q · (C q) = 2 C y³ / (1 - y)` with `kconst q = q²`.
* Live (Paired) closing for any charge `C ≤ 305` (`43 g ≤ 305`, i.e. `g ≤ 7`): `grouped_seed_error`,
  `grouped_weighted_error`, `grouped_middle_closing` (middle window `[2^-28, 3/2500]`, quadratic
  `767/1000 + 799/1000`), `grouped_tiny_quadratic` (tiny window: `3/2 + 799/1000 ≤ 3`). For `C ≤ 270` (`g ≤ 6`)
  `2 C ≤ 540`: the installed `errTot_toReal` / `canonical_seed_error` / `710/1000` chain applies verbatim.
-/

namespace ClaudeWCT.Arith.SideChannel.GroupedFamily
open SigGolfCandidate.T3 (Digest)
open Finset

/-- Chains of a `g`-leaf lower family: (leaf within the family, chain). -/
abbrev GChain (g : ℕ) := Fin g × Fin 43

/-- Evaluation point of a family chain: `(leaf mod g)·43 + chain + 1`. -/
def gpt {g : ℕ} (c : GChain g) : ℕ := c.1.val * 43 + c.2.val + 1

theorem gpt_injective (g : ℕ) : Function.Injective (gpt (g := g)) := by
  intro c c' h
  unfold gpt at h
  have h1 := c.2.isLt; have h2 := c'.2.isLt
  have e1 : c.1.val = c'.1.val := by omega
  have e2 : c.2.val = c'.2.val := by omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

theorem gpt_lt {g : ℕ} (hg : g ≤ 23) (c : GChain g) : gpt c < 1024 := by
  unfold gpt
  have h1 := c.1.isLt; have h2 := c.2.isLt
  have : c.1.val * 43 ≤ 22 * 43 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- Coefficients of a `g`-leaf family: 5 revealed seeds per leaf plus 3. -/
def gCount (g : ℕ) : ℕ := 5 * g + 3

/-- Reveal budget of a family whose leaves reveal at most 5 seeds each. -/
theorem revealed_card_le {g : ℕ} (Rev : Finset (GChain g))
    (h : ∀ l : Fin g, (Rev.filter fun c => c.1 = l).card ≤ 5) : Rev.card + 3 ≤ gCount g := by
  have hs : Rev.card = ∑ l : Fin g, (Rev.filter fun c => c.1 = l).card :=
    card_eq_sum_card_fiberwise (fun c _ => mem_univ c.1)
  have hle : ∑ l : Fin g, (Rev.filter fun c => c.1 = l).card ≤ ∑ _l : Fin g, 5 := sum_le_sum fun l _ => h l
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hle
  unfold gCount
  omega

/-- **Family side channel for `g` leaves** (`family_test_le` at `C = Fin g × Fin 43`, `pt = gpt`, `n = 5g + 3`). -/
theorem family_test_le_grouped {g : ℕ} (hg : g ≤ 23) (Rev : Finset (GChain g)) (hRev : Rev.card + 3 ≤ gCount g)
    (a : Free Rev) {α : Type} (A : (GChain g → Digest) → α → Prop)
    (tr : (GChain g → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin (gCount g) → Digest, prT (seedsY gpt Rev K) (A (seedsR gpt Rev K)) (tr (seedsR gpt Rev K)) ≤
      ∑ K : Fin (gCount g) → Digest,
          (∑ s, prT (seedsH gpt Rev a K s) (A (seedsR gpt Rev K)) (tr (seedsR gpt Rev K))) / Fintype.card Digest +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin (gCount g) → Digest, amLen (tr (seedsR gpt Rev K)) :=
  family_test_le (gpt_injective g) (gpt_lt hg) hRev a A tr D hD

theorem family_amLen_le_grouped {g : ℕ} (hg : g ≤ 23) (Rev : Finset (GChain g)) (hRev : Rev.card + 3 ≤ gCount g)
    {α : Type} (tr : (GChain g → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ)
    (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin (gCount g) → Digest, amLen (tr (seedsR gpt Rev K))) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤
      ∑ K : Fin (gCount g) → Digest, enT (seedsY gpt Rev K) (tr (seedsR gpt Rev K)) :=
  family_amLen_le (gpt_injective g) (gpt_lt hg) hRev tr D hD

/-! ### Any layer: `g` leaves of `w` chains, `r` reveals per leaf (top: `w = 54`, lower: `w = 43`) -/

/-- Chains of a `g`-leaf family whose leaves have `w` chains. -/
abbrev GChainW (g w : ℕ) := Fin g × Fin w

/-- Evaluation point `l·w + c + 1`. -/
def gptW {g w : ℕ} (c : GChainW g w) : ℕ := c.1.val * w + c.2.val + 1

theorem gptW_injective (g w : ℕ) : Function.Injective (gptW (g := g) (w := w)) := by
  intro c c' h
  unfold gptW at h
  have h1 := c.2.isLt; have h2 := c'.2.isLt
  have e1 : c.1.val = c'.1.val := by
    rcases Nat.lt_trichotomy c.1.val c'.1.val with hlt | heq | hgt
    · exfalso
      have : c.1.val * w + w ≤ c'.1.val * w := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      omega
    · exact heq
    · exfalso
      have : c'.1.val * w + w ≤ c.1.val * w := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hgt
      omega
  have e2 : c.2.val = c'.2.val := by rw [e1] at h; omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

theorem gptW_lt {g w : ℕ} (hgw : g * w < 1024) (c : GChainW g w) : gptW c < 1024 := by
  unfold gptW
  have h1 := c.1.isLt; have h2 := c.2.isLt
  have : c.1.val * w + w ≤ g * w := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h1
  omega

/-- Reveal budget with `r` reveals per leaf: `|Rev| + 3 ≤ r g + 3`. -/
theorem revealed_card_leW {g w r : ℕ} (Rev : Finset (GChainW g w))
    (h : ∀ l : Fin g, (Rev.filter fun c => c.1 = l).card ≤ r) : Rev.card + 3 ≤ r * g + 3 := by
  have hs : Rev.card = ∑ l : Fin g, (Rev.filter fun c => c.1 = l).card :=
    card_eq_sum_card_fiberwise (fun c _ => mem_univ c.1)
  have hle : ∑ l : Fin g, (Rev.filter fun c => c.1 = l).card ≤ ∑ _l : Fin g, r := sum_le_sum fun l _ => h l
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hle
  rw [Nat.mul_comm r g]
  omega

/-- **Family side channel for any layer**: `g` leaves of `w` chains (`g w < 1024`), `n ≥ |Rev| + 3` coefficients. -/
theorem family_test_le_groupedW {g w n : ℕ} (hgw : g * w < 1024) (Rev : Finset (GChainW g w))
    (hRev : Rev.card + 3 ≤ n) (a : Free Rev) {α : Type} (A : (GChainW g w → Digest) → α → Prop)
    (tr : (GChainW g w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, prT (seedsY gptW Rev K) (A (seedsR gptW Rev K)) (tr (seedsR gptW Rev K)) ≤
      ∑ K : Fin n → Digest,
          (∑ s, prT (seedsH gptW Rev a K s) (A (seedsR gptW Rev K)) (tr (seedsR gptW Rev K))) / Fintype.card Digest +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin n → Digest, amLen (tr (seedsR gptW Rev K)) :=
  family_test_le (gptW_injective g w) (gptW_lt hgw) hRev a A tr D hD

theorem family_amLen_le_groupedW {g w n : ℕ} (hgw : g * w < 1024) (Rev : Finset (GChainW g w))
    (hRev : Rev.card + 3 ≤ n) {α : Type} (tr : (GChainW g w → Digest) → OracleComp (TSpec (Free Rev) Digest) α)
    (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, amLen (tr (seedsR gptW Rev K))) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤
      ∑ K : Fin n → Digest, enT (seedsY gptW Rev K) (tr (seedsR gptW Rev K)) :=
  family_amLen_le (gptW_injective g w) (gptW_lt hgw) hRev tr D hD

/-- Top families of `g_top` leaves (54 chains each) fit the live closing iff `54 g_top ≤ 305`, i.e. `g_top ≤ 5`. -/
theorem top_group_charge : 54 * 5 ≤ 305 ∧ ¬ 54 * 6 ≤ 305 := by decide

/-- **Charge allocation** (generic `sum_NL_le`): if every entry is a test of at most one family and every family has at
most `C` chains in `chains`, the per-chain test counts sum to at most `C` times the number of entries. -/
theorem sum_charge_le {Ch F E : Type} [DecidableEq F] (chains : Finset Ch) (fam : Ch → F)
    (test : F → E → Prop) [∀ f e, Decidable (test f e)] (C : ℕ)
    (huniq : ∀ e f f', test f e → test f' e → f = f')
    (hsize : ∀ f, (chains.filter fun a => fam a = f).card ≤ C) (tr : List E) :
    ∑ a ∈ chains, (tr.filter fun e => decide (test (fam a) e)).length ≤ C * tr.length := by
  induction tr with
  | nil => simp
  | cons e tr ih =>
      have hs : ∀ a, (List.filter (fun e => decide (test (fam a) e)) (e :: tr)).length =
          (if test (fam a) e then 1 else 0) + (List.filter (fun e => decide (test (fam a) e)) tr).length := by
        intro a
        split_ifs with h1
        · rw [List.filter_cons_of_pos (by simpa using h1), List.length_cons]; omega
        · rw [List.filter_cons_of_neg (by simpa using h1), Nat.zero_add]
      simp only [hs, sum_add_distrib, List.length_cons]
      have he : ∑ a ∈ chains, (if test (fam a) e then 1 else 0) ≤ C := by
        by_cases hex : ∃ a ∈ chains, test (fam a) e
        · obtain ⟨a0, -, h0⟩ := hex
          rw [← sum_filter, sum_const, smul_eq_mul, mul_one]
          refine le_trans (card_le_card fun a ha => ?_) (hsize (fam a0))
          rw [mem_filter] at ha ⊢
          exact ⟨ha.1, huniq e _ _ ha.2 h0⟩
        · push_neg at hex
          rw [sum_eq_zero fun a ha => if_neg (hex a ha)]
          omega
      rw [Nat.mul_succ]
      omega

/-- With `kconst q = q²`: the per-test charge `errConst q · (C q)` is `2 C y³ / (1 - y)`, `y = q / 2^128`. -/
theorem seed_charge_real (q C : ℕ) :
    2 * ((2 : ℝ) ^ 128)⁻¹ ^ 3 * (kconst q : ℝ) / (1 - ((2 : ℝ) ^ 128)⁻¹ * q) * (C * q) =
      2 * C * ((q : ℝ) / 2 ^ 128) ^ 3 / (1 - (q : ℝ) / 2 ^ 128) := by
  unfold kconst
  push_cast
  rw [show ((2 : ℝ) ^ 128)⁻¹ * q = (q : ℝ) / 2 ^ 128 by ring]
  rw [div_mul_eq_mul_div]
  congr 1
  ring

end ClaudeWCT.Arith.SideChannel.GroupedFamily

namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

/-- Seed error of a `g`-leaf family charge `C ≤ 305` (`43 g ≤ 305`) on the live small window. -/
theorem grouped_seed_error (C y : ℝ) (hC0 : 0 ≤ C) (hC : C ≤ 305) (hy0 : 0 ≤ y) (hy : y ≤ 3 / 2500) :
    2 * C * y ^ 3 / (1 - y) ≤ (733 / 1000) * y ^ 2 := by
  have hd : 0 < 1 - y := by linarith
  apply (div_le_iff₀ hd).2
  have hcoef : 2 * C * y ≤ (733 / 1000) * (1 - y) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef (sq_nonneg y)]

/-- At `2 C ≤ 540` (`g ≤ 6`) the installed seed-error chain (`canonical_seed_error`) applies unchanged. -/
theorem grouped_seed_error_installed (C y : ℝ) (hC : 2 * C ≤ 540) (_hy0 : 0 ≤ y) (hy : y ≤ 3 / 2500) :
    2 * C * y ^ 3 / (1 - y) ≤ 540 * y ^ 3 / (1 - y) := by
  have hd : 0 < 1 - y := by linarith
  apply div_le_div_of_nonneg_right _ hd.le
  exact mul_le_mul_of_nonneg_right hC (by positivity)

/-- The weighting coefficients on the two small windows, with the error weight tightened to `1061/1000`
(exact values: middle `1.0470…` at `w = 1023/50000`, tiny `1.0600…` at `w = 3/100`). -/
theorem middle_coefficients_t (y : ℝ) (hy0 : 0≤y) (hy : y≤3/2500) :
    canonicalPrefix y (1023/50000)≤99847/50000 ∧
    canonicalEncoding y (1023/50000)≤99847/50000 ∧
    canonicalError y (1023/50000)≤1061/1000 :=
  ⟨(middle_coefficients y hy0 hy).1, (middle_coefficients y hy0 hy).2.1,
    (canonicalError_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans
      (by norm_num [canonicalError])⟩
theorem tiny_coefficients_t (y : ℝ) (hy0 : 0≤y) (hy : y≤1/2^28) :
    canonicalPrefix y (3/100)≤249/125 ∧ canonicalEncoding y (3/100)≤249/125 ∧
    canonicalError y (3/100)≤1061/1000 :=
  ⟨(tiny_coefficients y hy0 hy).1, (tiny_coefficients y hy0 hy).2.1,
    (canonicalError_mono hy0 hy (by norm_num) (by norm_num) (by norm_num)).trans
      (by norm_num [canonicalError])⟩
theorem grouped_weighted_error (y err coefficient : ℝ)
    (hc0 : 0 ≤ coefficient) (hc : coefficient ≤ 1061 / 1000)
    (he : err ≤ (733 / 1000) * y ^ 2) : coefficient * err ≤ (778 / 1000) * y ^ 2 := by
  calc coefficient * err ≤ coefficient * ((733 / 1000) * y ^ 2) := mul_le_mul_of_nonneg_left he hc0
    _ ≤ (1061 / 1000) * ((733 / 1000) * y ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by nlinarith [sq_nonneg y]

/-- Live middle window with the `g ≤ 7` family error: quadratic `767/1000 + 778/1000 = 1545/1000` (r3x: excess `149/125000`). -/
theorem grouped_middle_closing (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 3 / 2500) (hexcess : excess ≤ 149 / 125000) :
    (99847 / 50000) * y + y * excess + (1545 / 1000) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ (3 / 2500) * y := by
    nlinarith [mul_le_mul_of_nonneg_left hhigh hn]
  have habs : (1 : ℝ) / 2 ^ 136 ≤ y / 2 ^ 108 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 108 by positivity)
    norm_num at h ⊢
    linarith
  have h700 : (1 : ℝ) / 2 ^ 700 ≤ y / 2 ^ 672 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 672 by positivity)
    norm_num at h ⊢
    linarith
  have h152 : (1 : ℝ) / 2 ^ 152 ≤ y / 2 ^ 124 := by
    have h := div_le_div_of_nonneg_right hlow (show (0 : ℝ) ≤ 2 ^ 124 by positivity)
    norm_num at h ⊢
    linarith
  nlinarith

/-- Tiny window: the class budget `3/2` plus the family error `799/1000` stay below the installed `3`. -/
theorem grouped_tiny_quadratic : (3 / 2 : ℝ) + 778 / 1000 ≤ 3 := by norm_num

/-- The bound is sharp in `C`: `C = 306` already fails the middle window at `y = 3/2500` (absolute terms dropped). -/
theorem grouped_middle_fails_306 :
    let y : ℚ := 3 / 2500
    2 * y < 99847 / 50000 * y + y * (147 / 125000) + (767 / 1000 + 109 / 100 * (2 * 306 * y / (1 - y))) * y ^ 2 +
      y / 2 ^ 18 + y / 2 ^ 128 := by norm_num

#print axioms grouped_seed_error
#print axioms grouped_middle_closing
#print axioms grouped_middle_fails_306
end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

#print axioms ClaudeWCT.Arith.SideChannel.GroupedFamily.family_test_le_grouped
#print axioms ClaudeWCT.Arith.SideChannel.GroupedFamily.sum_charge_le
#print axioms ClaudeWCT.Arith.SideChannel.GroupedFamily.seed_charge_real
