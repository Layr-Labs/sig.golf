import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import SigGolfCandidate.Merge019
import SigGolfCandidate.Merge020

-- ==== merged from ClaudeWCT_Arith_GroupedFamily ====
section

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
theorem middle_coefficients_t (y : ℝ) (hy0 : 0≤y) (hy : y≤149/125000) :
    canonicalPrefix y (10297/500000)≤99843/50000 ∧
    canonicalEncoding y (10297/500000)≤99843/50000 ∧
    canonicalError y (10297/500000)≤1061/1000 :=
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

end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow

/-! RC938 closing at gate 791 (route C): near bank `378`, paired quadratic `18973/100`, charge `8077/10000`
(factor `4257/10^6 ≥ 1 - (θ-1)(1-y_s)`), middle quadratic `8077/10000 + 778/1000 = 15857/10000`, middle excess
budget `1153/10^6`; tiny class budget `18973/12000` (`+ 778/1000 ≤ 3`). -/
namespace SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 1024

theorem paired_partial_denominatorRC (y pwin : ℝ) (hy : y≤149/125000)
    (h : pwin≤(((19493/50)+1/1024)/(2*(1-y))+1/(2*(1-y)^2))*y^2) :
    pwin≤(19567/100)*y^2 := by
  have hd : 0<2*(1-y) := by linarith
  have hn : ((19493/50)+(1:ℝ)/1024)/(2*(1-y))≤1951632/10000 := by
    apply (div_le_iff₀ hd).2
    linarith
  have hbase : (124851:ℝ)/125000≤1-y := by linarith
  have hs : 0<2*(1-y)^2 := by positivity
  have hp : (1:ℝ)/(2*(1-y)^2)≤5012/10000 := by
    apply (div_le_iff₀ hs).2
    nlinarith [sq_nonneg (1-y-(124851:ℝ)/125000)]
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg y))

theorem chargeRC (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 149 / 125000)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ (19567 / 100) * y ^ 2) :
    z + near - (99843 / 50000) * z ≤ (8471 / 10000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (99843 / 50000) * z ≤ (4329 / 1000000) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem class_budgetRC (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 149 / 125000)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ (19567 / 100) * y ^ 2) :
    (99843 / 50000) * (p + e + m) + o + near ≤
      (99843 / 50000) * y + (8471 / 10000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := chargeRC y o near hy0 hy hn hcost hquad
  nlinarith

/-- Live middle window at gate 791: quadratic `8077/10000 + 778/1000 = 15857/10000`, excess `1153/10^6`. -/
theorem grouped_middle_closingRC (y excess : ℝ) (hlow : 1 / 2 ^ 28 ≤ y)
    (hhigh : y ≤ 149 / 125000) (hexcess : excess ≤ 1174 / 1000000) :
    (99843 / 50000) * y + y * excess + (16251 / 10000) * y ^ 2 + 1 / 2 ^ 136 +
      (y / 2 ^ 18 + 1 / 2 ^ 700 + 1 / 2 ^ 152 + y / 2 ^ 128) ≤ 2 * y := by
  have hn : 0 ≤ y := le_trans (by positivity) hlow
  have he := mul_le_mul_of_nonneg_left hexcess hn
  have hsq : y ^ 2 ≤ (149 / 125000) * y := by
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

theorem tiny_chargeRC (y z near : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ z)
    (hquad : near ≤ (19567 / 100) * y ^ 2) :
    z + near - (249 / 125) * z ≤ (19567 / 12000) * y ^ 2 := by
  have hny := mul_le_mul_of_nonneg_left hy1 hn
  have hz : z + near - (249 / 125) * z ≤ (1 / 120) * near := by
    nlinarith
  nlinarith [sq_nonneg y]

theorem tiny_class_budgetRC (p e o m y near : ℝ)
    (hp : 0 ≤ p) (he : 0 ≤ e) (ho : 0 ≤ o) (hm : 0 ≤ m)
    (hbudget : p + e + o + m ≤ y) (hy : y ≤ 1 / 2 ^ 28)
    (hn : 0 ≤ near) (hcost : near * (1 - y) ≤ o)
    (hquad : near ≤ (19567 / 100) * y ^ 2) :
    (249 / 125) * (p + e + m) + o + near ≤
      (249 / 125) * y + (19567 / 12000) * y ^ 2 := by
  have hy0 : 0 ≤ y := by linarith
  have hc := tiny_chargeRC y o near hy0 hy hn hcost hquad
  nlinarith

theorem grouped_tiny_quadraticRC : (19567 / 12000 : ℝ) + 778 / 1000 ≤ 3 := by norm_num

end SigGolfCandidate.Research.V7Composed198Closing.CanonicalWindow
end
-- ==== merged from ClaudeWCT_Arith_GroupedFamilyS ====
section

/-! # Family side channel with a point stride (r3-lean-seedfam)

`g` leaves of `w` chains, points `l·s + c + 1` with stride `s ≥ w` (lower `s = w = 43`; top `s = 64`, `w = 54`).
Injective, and below `1024` when `(g - 1)·s + w < 1024`. -/

namespace ClaudeWCT.Arith.SideChannel.GroupedFamily
open SigGolfCandidate.T3 (Digest)
open Finset

/-- Point of family chain `(l, c)` with stride `s`. -/
def gptS (s : ℕ) {g w : ℕ} (c : Fin g × Fin w) : ℕ := c.1.val * s + c.2.val + 1

theorem gptS_injective {s g w : ℕ} (hws : w ≤ s) : Function.Injective (gptS s (g := g) (w := w)) := by
  intro c c' h
  unfold gptS at h
  have h1 := c.2.isLt; have h2 := c'.2.isLt
  have e1 : c.1.val = c'.1.val := by
    rcases Nat.lt_trichotomy c.1.val c'.1.val with hlt | heq | hgt
    · exfalso
      have : c.1.val * s + s ≤ c'.1.val * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
      omega
    · exact heq
    · exfalso
      have : c'.1.val * s + s ≤ c.1.val * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hgt
      omega
  have e2 : c.2.val = c'.2.val := by rw [e1] at h; omega
  exact Prod.ext (Fin.ext e1) (Fin.ext e2)

theorem gptS_lt {s g w : ℕ} (hb : (g - 1) * s + w < 1024) (c : Fin g × Fin w) : gptS s c < 1024 := by
  unfold gptS
  have h1 := c.1.isLt; have h2 := c.2.isLt
  have : c.1.val * s ≤ (g - 1) * s := Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Family side channel with a stride.** -/
theorem family_test_le_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) (a : Free Rev) {α : Type}
    (A : (Fin g × Fin w → Digest) → α → Prop)
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest, prT (seedsY (gptS s) Rev K) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K)) ≤
      ∑ K : Fin n → Digest,
          (∑ x, prT (seedsH (gptS s) Rev a K x) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K))) /
            Fintype.card Digest +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K)) :=
  family_test_le (gptS_injective hws) (gptS_lt hb) hRev a A tr D hD

theorem family_test_ge_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) (a : Free Rev) {α : Type}
    (A : (Fin g × Fin w → Digest) → α → Prop)
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    ∑ K : Fin n → Digest,
        (∑ x, prT (seedsH (gptS s) Rev a K x) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K))) /
          Fintype.card Digest ≤
      ∑ K : Fin n → Digest, prT (seedsY (gptS s) Rev K) (A (seedsR (gptS s) Rev K)) (tr (seedsR (gptS s) Rev K)) +
        2 * ((Fintype.card Digest : ℝ)⁻¹) ^ 3 * kconst D *
          ∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K)) :=
  family_test_ge (gptS_injective hws) (gptS_lt hb) hRev a A tr D hD

theorem family_amLen_le_groupedS {s g w n : ℕ} (hws : w ≤ s) (hb : (g - 1) * s + w < 1024)
    (Rev : Finset (Fin g × Fin w)) (hRev : Rev.card + 3 ≤ n) {α : Type}
    (tr : (Fin g × Fin w → Digest) → OracleComp (TSpec (Free Rev) Digest) α) (D : ℕ) (hD : ∀ r, tdepth (tr r) ≤ D) :
    (∑ K : Fin n → Digest, amLen (tr (seedsR (gptS s) Rev K))) * (1 - (Fintype.card Digest : ℝ)⁻¹ * D) ≤
      ∑ K : Fin n → Digest, enT (seedsY (gptS s) Rev K) (tr (seedsR (gptS s) Rev K)) :=
  family_amLen_le (gptS_injective hws) (gptS_lt hb) hRev tr D hD

/-- v6 shapes: lower `7 × 43`, stride 43 (`6·43 + 43 = 301`); top `4 × 54`, stride 64 (`3·64 + 54 = 246`). -/
theorem v6_points : (7 - 1) * 43 + 43 < 1024 ∧ (4 - 1) * 64 + 54 < 1024 := by decide

end ClaudeWCT.Arith.SideChannel.GroupedFamily
end
-- ==== merged from ClaudeWCT_Arith_SideChannelSem ====
section

/-!
# Probabilistic semantics of test programs (campaign X1, stage B, item B3)

`evalT y p` runs a test program with uniform coins and tests answered against `y`; `exT y f p` is the expectation
of `f` defined by structural recursion (`prT` is the case of an indicator). This file links the recursive
quantities of `SideChannelComp` to the `PMF` semantics, and gives the generic lemma that `simulateQ` into `PMF`
commutes with a state-passing simulation (`simulateQ_run_stateT`), used to identify a stateful test program with
the oracle world it simulates.
-/

namespace ClaudeWCT.Arith.SideChannel

open OracleComp OracleSpec Finset ENNReal

variable {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] {α β : Type}

/-- Uniform coins. -/
noncomputable def coinImpl : QueryImpl unifSpec PMF := fun n => PMF.uniformOfFintype (Fin (n + 1))
/-- Tests answered against `y`. -/
noncomputable def testAns (y : ι → V) : QueryImpl ((ι × V) →ₒ Bool) PMF :=
  fun p : ι × V => PMF.pure (decide (y p.1 = p.2))
/-- Coins uniform, tests answered against `y`. -/
noncomputable def answerImpl (y : ι → V) : QueryImpl (TSpec ι V) PMF := coinImpl + testAns y

/-- The run of a test program against `y`. -/
noncomputable def evalT (y : ι → V) (oa : OracleComp (TSpec ι V) α) : PMF α := simulateQ (answerImpl y) oa

theorem evalT_pure (y : ι → V) (a : α) : evalT y (pure a : OracleComp (TSpec ι V) α) = PMF.pure a := rfl
theorem evalT_bind (y : ι → V) (oa : OracleComp (TSpec ι V) α) (f : α → OracleComp (TSpec ι V) β) :
    evalT y (oa >>= f) = (evalT y oa).bind (fun x => evalT y (f x)) := by
  unfold evalT
  rw [simulateQ_bind]
  rfl
theorem evalT_coinQ (y : ι → V) (n : ℕ) :
    evalT y (coinQ n : OracleComp (TSpec ι V) _) = PMF.uniformOfFintype (Fin (n + 1)) := by
  unfold evalT coinQ
  rw [simulateQ_spec_query]
  rfl
theorem evalT_testQ (y : ι → V) (p : ι × V) :
    evalT y (testQ p : OracleComp (TSpec ι V) Bool) = PMF.pure (decide (y p.1 = p.2)) := by
  unfold evalT testQ
  rw [simulateQ_spec_query]
  rfl
theorem evalT_coin (y : ι → V) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    evalT y (coinQ n >>= k) = (PMF.uniformOfFintype (Fin (n + 1))).bind (fun u => evalT y (k u)) := by
  rw [evalT_bind, evalT_coinQ]
theorem evalT_test (y : ι → V) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    evalT y (testQ p >>= k) = evalT y (k (decide (y p.1 = p.2))) := by
  rw [evalT_bind, evalT_testQ, PMF.pure_bind]

/-- Expectation of `f` over the run against `y`, by structural recursion. -/
noncomputable def exT (y : ι → V) (f : α → ℝ) : OracleComp (TSpec ι V) α → ℝ :=
  OracleComp.construct (C := fun _ => ℝ) f
    (fun t _ r => match t, r with
      | .inl n, r => (∑ u : Fin (n + 1), r u) / (n + 1)
      | .inr p, r => by classical exact r (decide (y p.1 = p.2)))

theorem exT_pure (y : ι → V) (f : α → ℝ) (a : α) : exT y f (pure a : OracleComp (TSpec ι V) α) = f a := rfl
theorem exT_coin (y : ι → V) (f : α → ℝ) (n : ℕ) (k : Fin (n + 1) → OracleComp (TSpec ι V) α) :
    exT y f (coinQ n >>= k) = (∑ u : Fin (n + 1), exT y f (k u)) / (n + 1) := rfl
theorem exT_test (y : ι → V) (f : α → ℝ) (p : ι × V) (k : Bool → OracleComp (TSpec ι V) α) :
    exT y f (testQ p >>= k) = exT y f (k (decide (y p.1 = p.2))) := rfl

theorem prT_eq_exT (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) :
    prT y A oa = exT y (fun a => by classical exact if A a then 1 else 0) oa := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih => rw [prT_coin, exT_coin]; simp only [ih]
  | test p k ih => rw [prT_test, exT_test]; exact ih _

theorem exT_bind (y : ι → V) (f : β → ℝ) (oa : OracleComp (TSpec ι V) α) (g : α → OracleComp (TSpec ι V) β) :
    exT y f (oa >>= g) = exT y (fun x => exT y f (g x)) oa := by
  induction oa using tinduction with
  | pure a => rw [pure_bind]; rfl
  | coin n k ih => rw [bind_assoc, exT_coin, exT_coin]; simp only [ih]
  | test p k ih => rw [bind_assoc, exT_test, exT_test]; exact ih _

theorem enT_bind (y : ι → V) (oa : OracleComp (TSpec ι V) α) (g : α → OracleComp (TSpec ι V) β) :
    enT y (oa >>= g) = enT y oa + exT y (fun x => enT y (g x)) oa := by
  induction oa using tinduction with
  | pure a => rw [pure_bind, enT_pure, exT_pure, zero_add]
  | coin n k ih =>
      rw [bind_assoc, enT_coin, enT_coin, exT_coin]
      simp only [ih, Finset.sum_add_distrib, add_div]
  | test p k ih =>
      rw [bind_assoc, enT_test, enT_test, exT_test, ih]
      ring

theorem exT_congr (y : ι → V) {f f' : α → ℝ} (h : ∀ x, f x = f' x) (oa : OracleComp (TSpec ι V) α) :
    exT y f oa = exT y f' oa := by
  rw [show f = f' from funext h]

theorem exT_nonneg (y : ι → V) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (oa : OracleComp (TSpec ι V) α) :
    0 ≤ exT y f oa := by
  induction oa using tinduction with
  | pure a => exact hf a
  | coin n k ih => rw [exT_coin]; exact div_nonneg (sum_nonneg fun u _ => ih u) (by positivity)
  | test p k ih => rw [exT_test]; exact ih _

/-- The recursive expectation is the `PMF` expectation (nonnegative payoffs). -/
theorem ofReal_exT (y : ι → V) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) (oa : OracleComp (TSpec ι V) α) :
    ENNReal.ofReal (exT y f oa) = ∑' x, evalT y oa x * ENNReal.ofReal (f x) := by
  induction oa using tinduction with
  | pure a =>
      rw [exT_pure, evalT_pure, tsum_eq_single a (fun b hb => by rw [PMF.pure_apply, if_neg hb, zero_mul]),
        PMF.pure_apply, if_pos rfl, one_mul]
  | coin n k ih =>
      rw [exT_coin, evalT_coin]
      simp only [PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
      simp_rw [← ENNReal.tsum_mul_right]
      rw [ENNReal.tsum_comm]
      simp_rw [mul_assoc, ENNReal.tsum_mul_left, ← ih]
      rw [tsum_fintype, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_sum_of_nonneg
        (fun u _ => exT_nonneg y hf (k u)), div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [mul_comm]
      congr 2
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  | test p k ih => rw [exT_test, evalT_test]; exact ih _

theorem ofReal_prT (y : ι → V) (A : α → Prop) (oa : OracleComp (TSpec ι V) α) :
    ENNReal.ofReal (prT y A oa) = by classical exact ∑' x, evalT y oa x * (if A x then 1 else 0) := by
  classical
  rw [prT_eq_exT, ofReal_exT y (fun x => by split <;> norm_num)]
  refine tsum_congr fun x => ?_
  split <;> simp

/-! ### State-passing simulations -/

/-- `simulateQ` into `PMF` commutes with a state-passing simulation into `OracleComp`. -/
theorem simulateQ_run_stateT {ιs ιt σ : Type} {spec : OracleSpec ιs} {τ : OracleSpec ιt}
    (h : QueryImpl τ PMF) (impl : QueryImpl spec (StateT σ (OracleComp τ))) (G : OracleComp spec α) (s : σ) :
    simulateQ h ((simulateQ impl G).run s) =
      (simulateQ (fun q => (StateT.mk fun s => simulateQ h ((impl q).run s) : StateT σ PMF _)) G).run s := by
  induction G using OracleComp.inductionOn generalizing s with
  | pure x => rfl
  | query_bind q k ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, StateT.run_mk]
      congr 1
      funext p
      exact ih p.1 p.2

/-! ### Depth and expectation under binds and simulations -/

theorem tdepth_bind_le (oa : OracleComp (TSpec ι V) α) (f : α → OracleComp (TSpec ι V) β) (D : ℕ)
    (h : ∀ x, tdepth (f x) ≤ D) : tdepth (oa >>= f) ≤ tdepth oa + D := by
  induction oa using tinduction with
  | pure a => rw [pure_bind]; exact (h a).trans (by rw [tdepth_pure, zero_add])
  | coin n k ih =>
      rw [bind_assoc, tdepth_coin, tdepth_coin]
      refine Finset.sup_le fun u _ => (ih u).trans ?_
      exact Nat.add_le_add_right (Finset.le_sup (f := fun u => tdepth (k u)) (Finset.mem_univ u)) D
  | test p k ih =>
      rw [bind_assoc, tdepth_test, tdepth_test]
      have h1 := ih true
      have h2 := ih false
      omega

theorem exT_const (y : ι → V) (c : ℝ) (oa : OracleComp (TSpec ι V) α) : exT y (fun _ => c) oa = c := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih =>
      rw [exT_coin]
      simp only [ih, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
  | test p k ih => rw [exT_test]; exact ih _

theorem exT_add_const (y : ι → V) (c : ℝ) (f : α → ℝ) (oa : OracleComp (TSpec ι V) α) :
    exT y (fun x => c + f x) oa = c + exT y f oa := by
  induction oa using tinduction with
  | pure a => rfl
  | coin n k ih =>
      rw [exT_coin, exT_coin]
      simp only [ih, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
  | test p k ih => rw [exT_test, exT_test]; exact ih _

/-- A state-passing simulation that tests at most once per `C`-query has test depth at most the `C`-query bound. -/
theorem tdepth_simulate_le {ιs σ : Type} {spec : OracleSpec ιs} (impl : QueryImpl spec (StateT σ (OracleComp (TSpec ι V))))
    (C : ιs → Prop) [DecidablePred C] (himpl : ∀ q s, tdepth ((impl q).run s) ≤ if C q then 1 else 0) :
    ∀ (G : OracleComp spec α) (n : ℕ) (s : σ), OracleComp.IsQueryBoundP G C n → tdepth ((simulateQ impl G).run s) ≤ n := by
  intro G
  induction G using OracleComp.inductionOn with
  | pure x => intro n s _; exact Nat.zero_le _
  | query_bind q k ih =>
      intro n s h
      rw [OracleComp.isQueryBoundP_query_bind_iff] at h
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      refine (tdepth_bind_le _ _ _ fun (p : spec.Range q × σ) => ih p.1 _ p.2 (h.2 p.1)).trans ?_
      have h1 := himpl q s
      split_ifs at h1 ⊢ with hc
      · rcases h.1 with h0 | h0
        · exact absurd hc h0
        · omega
      · omega

end ClaudeWCT.Arith.SideChannel
end
