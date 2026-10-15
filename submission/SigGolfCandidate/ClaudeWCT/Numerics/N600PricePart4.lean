import SigGolfCandidate.ClaudeWCT.Numerics.N600PricePart3

set_option Elab.async false



namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addEndpoint_ratio (d b : Nat) (h : addEndpoint d b) :
    (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^b := by
  have hh := geometric_add_interval d b h.1 h.2
  have hn : 0 ≤ (100/101 : ℝ)^d := by positivity
  have he : (101/100 : ℝ)^d*(100/101 : ℝ)^d=1 := by
    rw [← mul_pow]
    norm_num
  have h0 := mul_le_mul_of_nonneg_right hh.1 hn
  have h1 := mul_le_mul_of_nonneg_right hh.2 hn
  have hl : ((101/100 : ℝ)^(b+d)*(100/101))*(100/101 : ℝ)^d =
      (101/100 : ℝ)^b*(100/101) := by
    rw [pow_add]
    calc _ = ((101/100 : ℝ)^b*(100/101))*
        ((101/100 : ℝ)^d*(100/101 : ℝ)^d) := by ring
         _ = _ := by rw [he, mul_one]
  have hu : (101/100 : ℝ)^(b+d)*(100/101 : ℝ)^d=(101/100 : ℝ)^b := by
    rw [pow_add, mul_assoc, he, mul_one]
  rw [hl, add_mul, he, one_mul] at h0
  rw [hu, add_mul, he, one_mul] at h1
  exact ⟨h0,h1⟩

theorem pow_ratio_antitone (a b : Nat) (hab : a ≤ b) :
    (100/101 : ℝ)^b ≤ (100/101 : ℝ)^a := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  have hn : (100/101 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (mul_one _)

theorem add_run_ratio (e : Fin addRuns.length) (d : Nat)
    (hlo : addRuns[e].1 ≤ d) (hhi : d ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^addRuns[e].2.2*(100/101) ≤ 1+(100/101 : ℝ)^d ∧
      1+(100/101 : ℝ)^d ≤ (101/100 : ℝ)^addRuns[e].2.2 := by
  have he := add_run_bounds e
  have hl := (addEndpoint_ratio _ _ he.2.2.2.1).2
  have hh := (addEndpoint_ratio _ _ he.2.2.2.2).1
  exact ⟨hh.trans (add_le_add le_rfl (pow_ratio_antitone _ _ hhi)),
    (add_le_add le_rfl (pow_ratio_antitone _ _ hlo)).trans hl⟩

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathReflection
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem add_ratio_shift (i j b : Nat) (hj : j ≤ i)
    (h : (101/100 : ℝ)^b*(100/101) ≤ 1+(100/101 : ℝ)^(i-j) ∧
      1+(100/101 : ℝ)^(i-j) ≤ (101/100 : ℝ)^b) :
    (101/100 : ℝ)^(i+b)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(i+b) := by
  have he : (101/100 : ℝ)^(i-j)*(100/101 : ℝ)^(i-j)=1 := by
    rw [← mul_pow]
    norm_num
  have hid : (101/100 : ℝ)^i*(100/101 : ℝ)^(i-j)=(101/100 : ℝ)^j := by
    rw [show i=j+(i-j) by omega, pow_add]
    rw [show j+(i-j)-j=i-j by omega, mul_assoc, he, mul_one]
  have hlo := mul_le_mul_of_nonneg_left h.1 (show 0≤(101/100 : ℝ)^i by positivity)
  have hhi := mul_le_mul_of_nonneg_left h.2 (show 0≤(101/100 : ℝ)^i by positivity)
  have hl : (101/100 : ℝ)^i*((101/100 : ℝ)^b*(100/101)) =
      (101/100 : ℝ)^(i+b)*(100/101) := by rw [pow_add]; ring
  rw [hl, mul_add, mul_one, hid] at hlo
  rw [mul_add, mul_one, hid, ← pow_add] at hhi
  exact ⟨hlo,hhi⟩

theorem mergeBin_interval (e : Fin addRuns.length) (i j : Nat) (hj : j ≤ i)
    (hlo : addRuns[e].1 ≤ i-j) (hhi : i-j ≤ addRuns[e].2.1) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rw [mergeBin_forward e i j hj hlo hhi]
  exact add_ratio_shift i j _ hj (add_run_ratio e _ hlo hhi)

end ClaudeWCT.Numerics.SharedPathList

namespace ClaudeWCT.Numerics.SharedPathWinsor.Rows18
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A conservative scalar certificate for gate734/cap788. Its two moment
premises, at most6.9 and0.000772, still require a finite coverage proof. -/
theorem endpoint_middle :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (99847 / 50000 - 1 / 1024)) +
      193 / 250000 ≤ 147 / 125000 := by
  let x : ℝ := 6 * (99847 / 50000 - 1 / 1024) - 69 / 10
  have hx : (0 : ℝ) ≤ x := by norm_num [x]
  have he : (155 : ℝ) ≤ Real.exp x := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg hx 18)
    norm_num [x, Finset.sum_range_succ, Nat.factorial]
  have hi : (Real.exp x)⁻¹ ≤ (155 : ℝ)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos x) (by norm_num)).2 he
  have hn : 69 / 10 - 6 * (99847 / 50000 - 1 / 1024) = -x := by dsimp [x]; ring
  rw [hn, Real.exp_neg]
  norm_num at hi ⊢
  linarith

theorem endpoint_high :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (2 - 6 / 2500 - 1 / 1024)) +
      193 / 250000 ≤ 147 / 125000 := by
  have h := endpoint_middle
  have he := Real.exp_le_exp.mpr (show
      (69 / 10 - 6 * (2 - 6 / 2500 - 1 / 1024) : ℝ) ≤
        69 / 10 - 6 * (99847 / 50000 - 1 / 1024) by norm_num)
  linarith

theorem endpoint_low :
    (3 / 48 : ℝ) * Real.exp (69 / 10 - 6 * (1 - 1 / 1024)) +
      193 / 250000 ≤ 49 / 100 := by
  have hx : (69 / 10 - 6 * (1 - 1 / 1024) : ℝ) ≤ 1 := by norm_num
  have he := (Real.exp_le_exp.mpr hx).trans (le_of_lt Real.exp_one_lt_d9)
  nlinarith

end ClaudeWCT.Numerics.SharedPathWinsor.Rows18


namespace ClaudeWCT.Numerics.CanonicalCompression
open Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem fold_add_sum {α : Type} (xs : List α) (f : α → Nat) (a : Nat) :
    xs.foldl (fun s e => s + f e) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.add_assoc]

theorem filter_sum {α : Type} (p : α → Prop) [DecidablePred p]
    (f : α → Nat) (xs : List α) :
    ((xs.filter fun a => decide (p a)).map f).sum =
      (xs.map fun a => if p a then f a else 0).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hp : p x <;> simp [hp, ih]

theorem acceptedMass_sum (hist : List (Nat × Nat)) (floor : Nat) :
    acceptedMass hist floor = (hist.map fun e => if floor ≤ e.1 then e.2 else 0).sum := by
  rw [acceptedMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

theorem nextMass_sum (hist : List (Nat × Nat)) (floor residual : Nat) (next : Array Nat) :
    nextMass hist floor residual next =
      (hist.map fun e => if floor ≤ e.1 then e.2 * next[residual-e.1]?.getD 0 else 0).sum := by
  rw [nextMass, fold_add_sum, Nat.zero_add]
  exact filter_sum _ _ _

end ClaudeWCT.Numerics.CanonicalCompression
namespace ClaudeWCT.Numerics.CanonicalHistogram
open Finset CanonicalCompression
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem histogramWeight_sum (hist : List (Nat × Nat)) (credit : Nat) :
    histogramWeight hist credit =
      (hist.map fun e => if e.1 = credit then e.2 else 0).sum := by
  have he : (fun (s : Nat) (e : Nat × Nat) => if e.1 = credit then s + e.2 else s) =
      (fun s e => s + if e.1 = credit then e.2 else 0) := by
    funext s e
    split_ifs <;> simp
  rw [histogramWeight, he, fold_add_sum, Nat.zero_add]

theorem histogram_sum_weighted (hist : List (Nat × Nat)) (n : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) (f : Nat → Nat) :
    ∑ i : Fin n, histogramWeight hist i.val * f i.val =
      (hist.map fun e => e.2 * f e.1).sum := by
  induction hist with
  | nil => simp [histogramWeight_sum]
  | cons e hist ih =>
      have he : e.1 < n := hbound e List.mem_cons_self
      have hh : ∀ x ∈ hist, x.1 < n := fun x hx => hbound x (List.mem_cons_of_mem e hx)
      simp only [histogramWeight_sum, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib]
      simp_rw [← histogramWeight_sum]
      rw [ih hh]
      congr 1
      have ht : (fun i : Fin n => (if e.1 = i.val then e.2 else 0) * f i.val) =
          (fun i => if i = (⟨e.1, he⟩ : Fin n) then e.2 * f e.1 else 0) := by
        funext i
        by_cases hc : e.1 = i.val
        · have hi : i = (⟨e.1, he⟩ : Fin n) := Fin.ext hc.symm
          simp only [if_pos hc, if_pos hi]
          rw [hc]
        · have hi : i ≠ (⟨e.1, he⟩ : Fin n) := fun hi => hc (congrArg Fin.val hi).symm
          simp only [if_neg hc, if_neg hi, zero_mul]
      rw [ht]
      simp

theorem acceptedMass_finite (hist : List (Nat × Nat)) (n floor : Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    acceptedMass hist floor = ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val else 0 := by
  have h := histogram_sum_weighted hist n hbound (fun c => if floor ≤ c then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [acceptedMass_sum]
  simpa only [mul_ite, mul_one, mul_zero] using h.symm

theorem nextMass_finite (hist : List (Nat × Nat)) (n floor residual : Nat) (next : Array Nat)
    (hbound : ∀ e ∈ hist, e.1 < n) :
    nextMass hist floor residual next =
      ∑ i : Fin n, if floor ≤ i.val then histogramWeight hist i.val * next[residual-i.val]?.getD 0 else 0 := by
  have h := histogram_sum_weighted hist n hbound
    (fun c => if floor ≤ c then next[residual-c]?.getD 0 else 0)
  simp only [mul_ite, mul_zero] at h
  rw [nextMass_sum]
  exact h.symm

end ClaudeWCT.Numerics.CanonicalHistogram

namespace ClaudeWCT.Numerics.CanonicalCompression
open ENNReal
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem transition_enn (zn zd den weighted value rejected unit : Nat)
    (hzd : 0 < zd) (hden : 0 < den) (hunit : 0 < unit)
    (hsub : zn * rejected ≤ zd * den)
    (hrow : zn * weighted ≤ value * (zd * den - zn * rejected)) :
    ((zn : ENNReal) / zd) * ((weighted : ENNReal) / (den * unit) +
      ((rejected : ENNReal) / den) * ((value : ENNReal) / unit)) ≤ (value : ENNReal) / unit := by
  have hden0 : (den : ENNReal) ≠ 0 := by exact_mod_cast hden.ne'
  have hzd0 : (zd : ENNReal) ≠ 0 := by exact_mod_cast hzd.ne'
  have hunit0 : (unit : ENNReal) ≠ 0 := by exact_mod_cast hunit.ne'
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_natCast, Nat.cast_mul]
  exact transition_sound zn zd den weighted value rejected unit hzd hden hunit hsub hrow

theorem recurrenceCheck_sound (den : Nat) (hist : List (Nat × Nat))
    (floor residual : Nat) (next : Array Nat) (value : Nat)
    (hden : 0 < den) (hcheck : recurrenceCheck den hist floor residual next value = true) :
    1 ≤ (value : ENNReal) / scale ∧
    ((zNum : ENNReal) / zDen) *
      ((nextMass hist floor residual next : ENNReal) / (den * scale) +
       ((den - acceptedMass hist floor : Nat) : ENNReal) / den * ((value : ENNReal) / scale)) ≤
      (value : ENNReal) / scale := by
  simp only [recurrenceCheck, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with ⟨⟨⟨⟨hbase, hmass⟩, hnext⟩, hsub⟩, hrow⟩
  have hscale0 : (scale : ENNReal) ≠ 0 := by norm_num [scale]
  constructor
  · apply (ENNReal.toReal_le_toReal (by simp) (by finiteness)).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_div, ENNReal.toReal_natCast]
    apply (le_div_iff₀ (show (0 : ℝ) < scale by norm_num [scale])).2
    simpa using (show (scale : ℝ) ≤ value by exact_mod_cast hbase)
  · exact transition_enn zNum zDen den (nextMass hist floor residual next) value
      (den - acceptedMass hist floor) scale (by norm_num [zDen]) hden (by norm_num [scale])
      hsub.le hrow

end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedPathList
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- A coverage value and its conservatively rounded geometric bin. -/
structure RoundedInterval (loss bin : Nat) (x : ℝ) : Prop where
  nonneg : 0 ≤ x
  lower : (100/101 : ℝ)^loss * (101/100 : ℝ)^bin ≤ x
  upper : x ≤ (101/100 : ℝ)^bin

theorem RoundedInterval.mul {a b i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval b j y) :
    RoundedInterval (a+b) (i+j) (x*y) := by
  refine ⟨mul_nonneg hx.nonneg hy.nonneg, ?_, ?_⟩
  · calc
      (100/101 : ℝ)^(a+b) * (101/100 : ℝ)^(i+j) =
          ((100/101 : ℝ)^a * (101/100 : ℝ)^i) *
            ((100/101 : ℝ)^b * (101/100 : ℝ)^j) := by
              rw [pow_add, pow_add]
              ring
      _ ≤ x*y := mul_le_mul hx.lower hy.lower (by positivity) hx.nonneg
  · calc
      x*y ≤ (101/100 : ℝ)^i * (101/100 : ℝ)^j :=
        mul_le_mul hx.upper hy.upper hy.nonneg (by positivity)
      _ = _ := (pow_add _ _ _).symm

theorem RoundedInterval.add {a i j k : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hlo : (101/100 : ℝ)^k*(100/101) ≤
      (101/100 : ℝ)^i+(101/100 : ℝ)^j)
    (hhi : (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^k) :
    RoundedInterval (a+1) k (x+y) := by
  refine ⟨add_nonneg hx.nonneg hy.nonneg, ?_, (add_le_add hx.upper hy.upper).trans hhi⟩
  calc
    (100/101 : ℝ)^(a+1) * (101/100 : ℝ)^k =
        (100/101 : ℝ)^a * ((101/100 : ℝ)^k*(100/101)) := by
          rw [pow_succ]
          ring
    _ ≤ (100/101 : ℝ)^a * ((101/100 : ℝ)^i+(101/100 : ℝ)^j) :=
      mul_le_mul_of_nonneg_left hlo (by positivity)
    _ ≤ x+y := by rw [mul_add]; exact add_le_add hx.lower hy.lower

theorem RoundedInterval.prod {ι : Type} [DecidableEq ι]
    (s : Finset ι) (loss bin : ι → Nat) (x : ι → ℝ)
    (hx : ∀ i ∈ s, RoundedInterval (loss i) (bin i) (x i)) :
    RoundedInterval (∑ i ∈ s, loss i) (∑ i ∈ s, bin i) (∏ i ∈ s, x i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; constructor <;> norm_num
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hx i (Finset.mem_insert_self i s)).mul
      (ih (fun j hj => hx j (Finset.mem_insert_of_mem hj)))

theorem RoundedInterval.forest (bins : Fin 4 → Nat) (xs : Fin 4 → ℝ)
    (bin : Nat) (y : ℝ)
    (hx : ∀ i, RoundedInterval 3 (bins i) (xs i))
    (hy : RoundedInterval 1 bin y) :
    RoundedInterval 13 ((∑ i, bins i)+bin) ((∏ i, xs i)*y) := by
  have hp := RoundedInterval.prod Finset.univ (fun _ : Fin 4 => 3) bins xs
    (fun i _ => hx i)
  have hc : (∑ _i : Fin 4, (3 : Nat)) = 12 := by decide
  rw [hc] at hp
  exact hp.mul hy

theorem RoundedInterval.fee_bounds {bin : Nat} {x : ℝ}
    (hx : RoundedInterval 13 bin x) :
    ClaudeWCT.Numerics.SharedFees.lowerValue bin ≤ (734 : ℝ)/2^66*x ∧
      (734 : ℝ)/2^66*x ≤ ClaudeWCT.Numerics.SharedFees.upperValue bin := by
  simp only [ClaudeWCT.Numerics.SharedFees.lowerValue_power,
    ClaudeWCT.Numerics.SharedFees.upperValue_power]
  constructor
  · have h := mul_le_mul_of_nonneg_left hx.lower (by positivity : (0 : ℝ) ≤ 734/2^66)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  · exact mul_le_mul_of_nonneg_left hx.upper (by positivity)

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem finite_bin_rebate {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight : α → ℝ) (rebate : Nat → ℝ) :
    (∑ j ∈ range n,
      (∑ a, if good a ∧ bin a=j then weight a else 0)*rebate j) =
    ∑ a, if good a ∧ bin a<n then weight a*rebate (bin a) else 0 := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hg : good a
  · simp only [hg, true_and, ite_mul, zero_mul]
    simp [Finset.mem_range, eq_comm]
  · simp [hg]

/-- A lower histogram certifies a rebate from a global cost bound. Histories
omitted by the histogram retain the full global cost. -/
theorem histogram_fee_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin : α → Nat)
    (weight cost : α → ℝ) (lower fee : Nat → ℝ) (κ G : ℝ)
    (hκ : 0 ≤ κ)
    (hfee : ∀ j, j<n → fee j ≤ G)
    (hlower : ∀ j, j<n → lower j ≤
      ∑ a, if good a ∧ bin a=j then weight a else 0)
    (hglobal : ∀ a, cost a ≤ κ*weight a*G)
    (hlocal : ∀ a, good a → bin a<n → cost a ≤ κ*weight a*fee (bin a)) :
    (∑ a, cost a) + κ*(∑ j ∈ range n, lower j*(G-fee j)) ≤
      κ*(∑ a, weight a)*G := by
  classical
  have hpoint (a : α) : cost a +
      κ*(if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0) ≤
        κ*weight a*G := by
    by_cases hg : good a ∧ bin a<n
    · rw [if_pos hg]
      nlinarith [hlocal a hg.1 hg.2]
    · rw [if_neg hg, mul_zero, add_zero]
      exact hglobal a
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset α)) (fun a _ => hpoint a)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hs
  have hrebate : (∑ j ∈ range n, lower j*(G-fee j)) ≤
      ∑ a, if good a ∧ bin a<n then weight a*(G-fee (bin a)) else 0 := by
    rw [← finite_bin_rebate n good bin weight (fun j => G-fee j)]
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_right (hlower j (Finset.mem_range.mp hj))
      (sub_nonneg.mpr (hfee j (Finset.mem_range.mp hj)))
  exact (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hrebate hκ)).trans hs

end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem packFun_finset_sum {ι : Type} (s : Finset ι) (B n : Nat) (f : ι → Nat → Nat) :
    packFun B n (fun j => ∑ i ∈ s, f i j) = ∑ i ∈ s, packFun B n (f i) := by
  unfold packFun
  simp_rw [Finset.sum_mul]
  exact Finset.sum_comm

theorem sum_eq_packFun {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (ha : ∀ i ∈ s, a i < B^n) :
    (∑ i ∈ s, a i) = packFun B n (fun j => ∑ i ∈ s, digit B (a i) j) := by
  rw [packFun_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [packFun_digits, Nat.mod_eq_of_lt (ha i hi)]

theorem digit_sum_of_bound {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B)
    (j : Nat) (hj : j < n) :
    digit B (∑ i ∈ s, a i) j = ∑ i ∈ s, digit B (a i) j := by
  rw [sum_eq_packFun s B n a ha]
  exact digit_packFun B n _ hB hc j hj

theorem sum_packed_lt {ι : Type} (s : Finset ι) (B n : Nat) (a : ι → Nat)
    (hB : 0 < B) (ha : ∀ i ∈ s, a i < B^n)
    (hc : ∀ j, j < n → (∑ i ∈ s, digit B (a i) j) < B) :
    (∑ i ∈ s, a i) < B^n := by
  rw [sum_eq_packFun s B n a ha]
  exact packFun_lt B n _ hB hc

theorem digit_polynomial_eval (P : Nat[X]) (B n : Nat)
    (hB : 0 < B) (hc : ∀ j, j < n → P.coeff j < B)
    (hz : ∀ j, n ≤ j → P.coeff j = 0)
    (j : Nat) (hj : j < n) : digit B (P.eval B) j = P.coeff j := by
  rw [polynomial_eval_packFun P B n hz]
  exact digit_packFun B n _ hB hc j hj

end ClaudeWCT.Numerics.SharedDigitBlock


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem weightedHistogram_selector_split {α : Type} [Fintype α] (r : Nat)
    (good : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Prop)
    (bin weight : (t u : Nat) → (Fin t → α) → (Fin t → α) →
      (Fin u → α) → (Fin u → α) → Nat) :
    weightedHistogram
      (fun h : (Fin r → Fin 2) × (Fin r → α) × (Fin r → α) =>
        good (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => bin (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1))
      (fun h => weight (occ h.1 0) (occ h.1 1)
          (splitRanks h.1 h.2.1 0) (splitRanks h.1 h.2.2 0)
          (splitRanks h.1 h.2.1 1) (splitRanks h.1 h.2.2 1)) =
    ∑ t ∈ range (r+1), r.choose t •
      weightedHistogram
        (fun h : ((Fin t → α) × (Fin t → α)) ×
          ((Fin (r-t) → α) × (Fin (r-t) → α)) =>
            good t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => bin t (r-t) h.1.1 h.1.2 h.2.1 h.2.2)
        (fun h => weight t (r-t) h.1.1 h.1.2 h.2.1 h.2.2) := by
  classical
  unfold weightedHistogram
  simp only [Fintype.sum_prod_type]
  exact sum_pair_split r (fun t u A₀ B₀ A₁ B₁ =>
    if good t u A₀ B₀ A₁ B₁ then
      C (weight t u A₀ B₀ A₁ B₁)*X^(bin t u A₀ B₀ A₁ B₁) else 0)

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathList
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev AddPiece := Fin addRuns.length × Bool

def addPieceGood (e : AddPiece) (i j : Nat) : Prop :=
  if e.2 then i<j ∧ addRuns[e.1].1 ≤ j-i ∧ j-i ≤ addRuns[e.1].2.1
  else j ≤ i ∧ addRuns[e.1].1 ≤ i-j ∧ i-j ≤ addRuns[e.1].2.1

def addPieceBin (e : AddPiece) (i j : Nat) : Nat :=
  (if e.2 then j else i)+addRuns[e.1].2.2

theorem addPiece_unique (e f : AddPiece) (i j : Nat)
    (he : addPieceGood e i j) (hf : addPieceGood f i j) : e=f := by
  rcases e with ⟨e,be⟩
  rcases f with ⟨f,bf⟩
  cases be <;> cases bf <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he hf
  · exact Prod.ext (add_run_unique e f (i-j) he.2 hf.2) rfl
  · omega
  · omega
  · exact Prod.ext (add_run_unique e f (j-i) he.2 hf.2) rfl

theorem addPiece_bin (e : AddPiece) (i j : Nat) (he : addPieceGood e i j) :
    addPieceBin e i j=mergeBin i j := by
  rcases e with ⟨e,b⟩
  cases b <;> simp only [addPieceGood, Bool.false_eq_true, if_false, if_true] at he
  · exact (mergeBin_forward e i j he.1 he.2.1 he.2.2).symm
  · rw [mergeBin_comm]
    exact (mergeBin_forward e j i (Nat.le_of_lt he.1) he.2.1 he.2.2).symm

theorem pair_partition_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop) (ba wa : α → Nat) (bb wb : β → Nat) :
    CoeffLE (∑ e : AddPiece,
      weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
        (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
      (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
        (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)) := by
  apply weightedHistogram_partition
  · intro e p hp
    exact ⟨hp.1,hp.2.1⟩
  · intro e p hp
    exact addPiece_bin e _ _ hp.2.2
  · intro e f p he hf
    exact addPiece_unique e f _ _ he.2.2 hf.2.2

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset ClaudeWCT.Numerics.N600
set_option maxHeartbeats 2000000

theorem coordinate_coverage_pos {β C : Type} [Fintype β] [Fintype C] [DecidableEq C]
    (val : β → Fin 6 → Nat) {r : Nat} (hr : 0<r) (E : Fin r → C×β) :
    0<coordinateCoverage val E := by
  classical
  unfold coordinateCoverage
  apply Finset.card_pos.mpr
  refine ⟨E ⟨0,hr⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
  intro i
  exact ⟨⟨0,hr⟩,rfl,le_rfl⟩

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem paidPlain_sums (B : Nat) (fs : List (Nat × Nat)) (p : Nat) :
    paidPlain B fs p =
      (∑ i : Fin fs.length, digit B p i.val,
       ∑ i : Fin fs.length, digit B p i.val * fs[i].1,
       ∑ i : Fin fs.length, digit B p i.val * fs[i].2) := by
  induction fs generalizing p with
  | nil => simp only [paidPlain, List.length_nil, Fin.sum_univ_zero]
  | cons e fs ih =>
    rw [paidPlain, ih]
    simp only [List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, List.getElem_cons_zero, List.getElem_cons_succ, Fin.val_zero, Fin.val_succ,
      digit, Nat.pow_zero, Nat.div_one, Nat.pow_succ,
      Nat.div_div_eq_div_mul, Nat.mul_comm]

theorem paidTree_polynomial (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j < 2^4096) :
    paidTree fuel fs (P.eval (2^4096)) =
      (∑ i : Fin fs.length, P.coeff i.val,
       ∑ i : Fin fs.length, P.coeff i.val * fs[i].1,
       ∑ i : Fin fs.length, P.coeff i.val * fs[i].2) := by
  rw [paidTree_plain, paidPlain_sums]
  have hd (i : Nat) : digit (2^4096) (P.eval (2^4096)) i = P.coeff i :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) i P hc
  simp only [hd]

theorem paidTree_polynomial_mass (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j < 2^4096) :
    (paidTree fuel fs (P.eval (2^4096))).1 ≤ P.eval 1 := by
  rw [paidTree_polynomial fuel fs P hc]
  dsimp only
  rw [Fin.sum_univ_eq_sum_range]
  exact ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one P (Finset.range fs.length)

end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Disjoint retained pieces may be added in packed form without a carry.
The bound comes from the mass of the actual history space. -/
theorem packed_histogram_sum_lower {ι α : Type} [Fintype ι] [Fintype α]
    (B n M : Nat) (hB : 0<B)
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (p : ι → Nat) (P : ι → Nat[X])
    (hp : ∀ e, p e<B^n)
    (hd : ∀ e j, j<n → digit B (p e) j≤(P e).coeff j)
    (hP : CoeffLE (∑ e, P e) (weightedHistogram good bin weight))
    (hM : ∀ a, good a → weight a≤M) (hmass : Fintype.card α*M<B) :
    (∑ e, p e)<B^n ∧
      ∀ j, j<n → digit B (∑ e, p e) j≤(weightedHistogram good bin weight).coeff j := by
  have hc (j : Nat) (hj : j<n) :
      (∑ e, digit B (p e) j)<B := by
    calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
         _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
         _ ≤ (weightedHistogram good bin weight).coeff j := hP j
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_coeff_le_mass _ _
         _ ≤ Fintype.card α*M := weightedHistogram_mass_le good bin weight M hM
         _ < B := hmass
  refine ⟨sum_packed_lt univ B n p hB (fun e _ => hp e) hc, ?_⟩
  intro j hj
  rw [digit_sum_of_bound univ B n p hB (fun e _ => hp e) hc j hj]
  calc _ ≤ ∑ e, (P e).coeff j := Finset.sum_le_sum (fun e _ => hd e j hj)
       _ = (∑ e, P e).coeff j := (Polynomial.finset_sum_coeff _ _ _).symm
       _ ≤ _ := hP j

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedCoverage
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem directed_cross_small {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (ap af bp bf : Nat → Nat)
    (haP : ∀ i, ap i ≤ ∑ a, if ga a ∧ ba a=i then 1 else 0)
    (haF : ∀ i, af i ≤ ∑ a, if ga a ∧ ba a=i then wa a else 0)
    (hbP : ∀ j, bp j ≤ ∑ b, if gb b ∧ bb b=j then 1 else 0)
    (hbF : ∀ j, bf j ≤ ∑ b, if gb b ∧ bb b=j then wb b else 0)
    (Ma Mb B : Nat) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hB : Fintype.card α*Fintype.card β*(Ma+Mb)<B)
    (i : Nat) (s : Finset Nat) :
    af i*(∑ j ∈ s, bp j) + ap i*(∑ j ∈ s, bf j)<B := by
  apply (directed_fiber_lower ga gb ba wa bb wb ap af bp bf haP haF hbP hbF i s).trans_lt
  calc (∑ p : α×β, if (ga p.1 ∧ ba p.1=i) ∧ (gb p.2 ∧ bb p.2∈s)
          then wa p.1+wb p.2 else 0) ≤ ∑ _p : α×β, (Ma+Mb) := by
        apply Finset.sum_le_sum
        intro p _
        split_ifs
        · exact Nat.add_le_add (hwa p.1) (hwb p.2)
        · exact Nat.zero_le _
       _ = Fintype.card α*Fintype.card β*(Ma+Mb) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
          nsmul_eq_mul, Nat.cast_id]
       _ < B := hB

end ClaudeWCT.Numerics.SharedCoverage


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset
open ClaudeWCT.Numerics.SharedPathList (Cell addRuns)
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem fold_add_pair {α : Type} (xs : List α) (f g : α → Nat) (acc : Nat) :
    xs.foldl (fun s e => s+f e+g e) acc =
      acc+(xs.map (fun e => f e+g e)).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih => simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]; omega

theorem list_sum_fin {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map f).sum = ∑ i : Fin xs.length, f xs[i] := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero, List.getElem_cons_succ]

def addPieceValue (a b : Cell) (e : Fin addRuns.length × Bool) : Nat :=
  if e.2 then
    if addRuns[e.1].2.1=0 then 0 else
      directedFirst b (prefixes a.1, prefixes a.2)
        (max 1 addRuns[e.1].1) addRuns[e.1].2.1 addRuns[e.1].2.2
  else directedFirst a (prefixes b.1, prefixes b.2)
      addRuns[e.1].1 addRuns[e.1].2.1 addRuns[e.1].2.2

theorem addFirst_eq_piece_sum (a b : Cell) :
    addFirst a b = ∑ e : Fin addRuns.length × Bool, addPieceValue a b e := by
  rw [addFirst, fold_add_pair, Nat.zero_add, list_sum_fin]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [addPieceValue, Nat.add_comm]

theorem addPieceValue_bound (a b : Cell) (e : Fin addRuns.length × Bool) :
    addPieceValue a b e < (2^1024)^2048 := by
  have hb (a pref : Cell) (lo hi shift : Nat) :
      directedFirst a pref lo hi shift < (2^1024)^2048 := by
    unfold directedFirst cutMask
    simp only [Nat.shiftLeft_eq, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod, ←pow_mul]
    exact Nat.mod_lt _ (by positivity)
  unfold addPieceValue
  split_ifs
  · positivity
  · exact hb _ _ _ _ _
  · exact hb _ _ _ _ _

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem addFirst_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat) (a b : Cell)
    (Ma Mb : Nat) (hwa : ∀ x, wa x≤Ma) (hwb : ∀ y, wb y≤Mb)
    (hmass : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (hpiece : ∀ (e : AddPiece) j, j<2048 →
      digit (2^1024) (addPieceValue a b e) j ≤
        (weightedHistogram
          (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
          (fun p => addPieceBin e (ba p.1) (bb p.2))
          (fun p => wa p.1+wb p.2)).coeff j) :
    addFirst a b<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (addFirst a b) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  rw [addFirst_eq_piece_sum]
  apply packed_histogram_sum_lower (2^1024) 2048 (Ma+Mb) (by positivity)
    (fun p : α×β => ga p.1 ∧ gb p.2)
    (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)
    (addPieceValue a b)
    (fun e => weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ addPieceGood e (ba p.1) (bb p.2))
      (fun p => addPieceBin e (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2))
    (addPieceValue_bound a b) hpiece (pair_partition_lower ga gb ba wa bb wb)
  · intro p _
    exact Nat.add_le_add (hwa p.1) (hwb p.2)
  · simpa only [Fintype.card_prod] using hmass

end ClaudeWCT.Numerics.SharedPathPacked


namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Exact integer accounting of retained fees and omitted first moment. -/
theorem histogram_paid_bound {α : Type} [Fintype α]
    (n : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (cost : α → ℝ) (lower fee : Nat → Nat) (κ : ℝ) (G : Nat)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hlower : ∀ j, j<n → lower j≤∑ a, if good a ∧ bin a=j then weight a else 0)
    (hmass : (∑ j ∈ range n, lower j)≤∑ a, weight a)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, lower j*fee j) +
      G*((∑ a, weight a)-(∑ j ∈ range n, lower j)) : Nat) : ℝ)) := by
  classical
  have h := histogram_fee_bound n good bin (fun a => (weight a : ℝ)) cost
    (fun j => (lower j : ℝ)) (fun j => (fee j : ℝ)) κ (G : ℝ) hκ
    (fun j hj => by exact_mod_cast hfee j hj)
    (fun j hj => by exact_mod_cast hlower j hj) hglobal hlocal
  have he : (∑ j ∈ range n, (lower j : ℝ)*((G : ℝ)-(fee j : ℝ))) =
      (G : ℝ)*(∑ j ∈ range n, (lower j : ℝ))-
        ∑ j ∈ range n, (lower j : ℝ)*(fee j : ℝ) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ←Finset.sum_mul]
    ring
  rw [he] at h
  push_cast [Nat.cast_sub hmass]
  nlinarith [h]

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem ceilDiv_mul_ge_left (n d : Nat) (hd : 0 < d) : n ≤ d * ceilDiv n d := by
  unfold ceilDiv
  have hrem := Nat.mod_lt (n + d - 1) hd
  have hdiv := Nat.mod_add_div (n + d - 1) d
  omega

theorem mulUp_sound (a b : Nat) :
    (a : ℝ) / scale * ((b : ℝ) / scale) ≤ (mulUp a b : ℝ) / scale := by
  have hs : 0 < scale := by norm_num [scale]
  have hh := ceilDiv_mul_ge_left (a*b) scale hs
  have hc : (a : ℝ) * b ≤ (scale : ℝ) * mulUp a b := by
    exact_mod_cast hh
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  rw [div_mul_div_comm]
  apply (div_le_div_iff₀ (mul_pos hsR hsR) hsR).2
  nlinarith

/-- The reflected repeated-squaring evaluator rounds every multiplication up. -/
theorem powerUp_sound (base exponent : Nat) :
    ((base : ℝ) / scale) ^ exponent ≤ (powerUp base exponent : ℝ) / scale := by
  induction exponent using Nat.strong_induction_on generalizing base with
  | h exponent ih =>
      rw [powerUp]
      by_cases he : exponent = 0
      · simp [he, scale]
      · rw [if_neg he]
        have hhalf : exponent / 2 < exponent := Nat.div_lt_self (Nat.pos_of_ne_zero he) (by decide)
        have hi := ih (exponent / 2) hhalf (mulUp base base)
        have hbase : (0 : ℝ) ≤ (base : ℝ) / scale := by positivity
        have hsq : ((base : ℝ) / scale) ^ 2 ≤ (mulUp base base : ℝ) / scale := by
          simpa only [pow_two] using mulUp_sound base base
        have hh : ((base : ℝ) / scale) ^ (2 * (exponent / 2)) ≤
            (powerUp (mulUp base base) (exponent / 2) : ℝ) / scale := by
          rw [pow_mul]
          exact (pow_le_pow_left₀ (sq_nonneg _) hsq _).trans hi
        split_ifs with hp
        · convert hh using 1
          congr 1
          omega
        · have hm : exponent % 2 = 1 := by omega
          have hrepr : exponent = 1 + 2 * (exponent / 2) := by omega
          conv_lhs => rw [hrepr, pow_add, pow_one]
          exact (mul_le_mul_of_nonneg_left hh hbase).trans
            (mulUp_sound base (powerUp (mulUp base base) (exponent / 2)))

end ClaudeWCT.Numerics.CanonicalCompression


namespace ClaudeWCT.Numerics.SharedDigitBlock
open Finset Polynomial ClaudeWCT.Numerics.N600
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable def packedPoly (B n p : Nat) : Nat[X] := polyOf n (digit B p)

theorem packedPoly_eval (B n p : Nat) (hp : p<B^n) :
    (packedPoly B n p).eval B=p := by
  rw [packedPoly, polyOf_eval, packFun_digits, Nat.mod_eq_of_lt hp]

theorem packedPoly_coeff_lt (B n p : Nat) (hB : 0<B) (j : Nat) :
    (packedPoly B n p).coeff j<B := by
  rw [packedPoly, polyOf_coeff]
  split_ifs
  · exact Nat.mod_lt _ hB
  · exact hB

theorem packedPoly_below (B n p : Nat) (Q : Nat[X])
    (hd : ∀ j, j<n → digit B p j≤Q.coeff j) :
    CoeffLE (packedPoly B n p) Q := by
  intro j
  rw [packedPoly, polyOf_coeff]
  split_ifs with hj
  · exact hd j hj
  · exact Nat.zero_le _

theorem changeBase_polynomial (B C h p : Nat) (hB : 0<B) (hp : p<B^(2^h)) :
    changeBase B C h p=(packedPoly B (2^h) p).eval C := by
  rw [changeBase_model B C hB h p hp, packedPoly, polyOf_eval]

end ClaudeWCT.Numerics.SharedDigitBlock

namespace ClaudeWCT.Numerics.SharedPathPacked
open Polynomial ClaudeWCT.Numerics.SharedDigitBlock
set_option maxHeartbeats 2000000

theorem spread_polynomial (h p : Nat) (hp : p<(2^1024)^(2^h)) :
    spread h p=(packedPoly (2^1024) (2^h) p).eval (2^4096) := by
  rw [spread_eq_changeBase]
  exact changeBase_polynomial _ _ h p (by positivity) hp

theorem forest_packed_polynomial (p q : Nat)
    (hp : p<(2^1024)^2048) (hq : q<(2^1024)^1024) :
    (spread 11 p)^4*spread 10 q =
      ((packedPoly (2^1024) 2048 p)^4*packedPoly (2^1024) 1024 q).eval (2^4096) := by
  have hp' : p<(2^1024)^(2^11) := by simpa only [show (2:Nat)^11=2048 from rfl] using hp
  have hq' : q<(2^1024)^(2^10) := by simpa only [show (2:Nat)^10=1024 from rfl] using hq
  rw [spread_polynomial 11 p hp', spread_polynomial 10 q hq']
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    show (2:Nat)^11=2048 from rfl, show (2:Nat)^10=1024 from rfl]

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem histogram_moment_bound {α : Type} [Fintype α]
    (n total G : Nat) (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a)=total)
    (cost : α → ℝ) (fee : Nat → Nat) (κ : ℝ)
    (hκ : 0≤κ) (hfee : ∀ j, j<n → fee j≤G)
    (hglobal : ∀ a, cost a≤κ*(weight a : ℝ)*G)
    (hlocal : ∀ a, good a → bin a<n → cost a≤κ*(weight a : ℝ)*(fee (bin a) : ℝ)) :
    (∑ a, cost a)≤κ*((((∑ j ∈ range n, P.coeff j*fee j) +
      G*(total-(∑ j ∈ range n, P.coeff j)) : Nat) : ℝ)) := by
  classical
  have hm : (∑ j ∈ range n, P.coeff j)≤∑ a, weight a := by
    calc _ ≤ P.eval 1 := sum_coeff_le_eval_one P (range n)
         _ ≤ (weightedHistogram good bin weight).eval 1 := polynomial_mass_mono hP
         _ = ∑ a, if good a then weight a else 0 := weightedHistogram_eval_one good bin weight
         _ ≤ ∑ a, weight a := Finset.sum_le_sum (fun a _ => by split_ifs <;> omega)
  have h := histogram_paid_bound n good bin weight cost P.coeff fee κ G hκ hfee
    (fun j _ => by simpa only [weightedHistogram_coeff] using hP j) hm hglobal hlocal
  simpa only [htotal] using h

theorem sum_fin_list_getD {α : Type} (fs : List α) (fallback : α) (f : Nat → α → Nat) :
    (∑ i : Fin fs.length, f i.val fs[i]) =
      ∑ j ∈ range fs.length, f j (fs[j]?.getD fallback) := by
  calc _ = ∑ i : Fin fs.length, f i.val (fs[i.val]?.getD fallback) := by
         apply Finset.sum_congr rfl
         intro i _
         simp only [List.getElem?_eq_getElem i.isLt, Option.getD_some, Fin.getElem_fin]
       _ = _ := Fin.sum_univ_eq_sum_range (fun j => f j (fs[j]?.getD fallback)) fs.length

theorem paidTree_polynomial_range (fuel : Nat) (fs : List (Nat × Nat)) (P : Nat[X])
    (hc : ∀ j, P.coeff j<2^4096) :
    paidTree fuel fs (P.eval (2^4096)) =
      (∑ j ∈ range fs.length, P.coeff j,
       ∑ j ∈ range fs.length, P.coeff j*(fs[j]?.getD (0,0)).1,
       ∑ j ∈ range fs.length, P.coeff j*(fs[j]?.getD (0,0)).2) := by
  rw [paidTree_polynomial fuel fs P hc, Fin.sum_univ_eq_sum_range,
    sum_fin_list_getD fs (0,0) (fun j e => P.coeff j*e.1),
    sum_fin_list_getD fs (0,0) (fun j e => P.coeff j*e.2)]

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.CanonicalCompression
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem acceptedMass_antitone (hist : List (Nat × Nat)) {floor lower : Nat} (hle : lower ≤ floor) :
    acceptedMass hist floor ≤ acceptedMass hist lower := by
  induction hist with
  | nil => simp [acceptedMass_sum]
  | cons e hist ih =>
      simp only [acceptedMass_sum, List.map_cons, List.sum_cons] at ih ⊢
      by_cases hf : floor ≤ e.1
      · have hl := hle.trans hf
        simp only [if_pos hf, if_pos hl]
        omega
      · by_cases hl : lower ≤ e.1
        · simp only [if_neg hf, if_pos hl]
          omega
        · simp only [if_neg hf, if_neg hl]
          simpa only [Nat.zero_add] using ih

end ClaudeWCT.Numerics.CanonicalCompression

namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem prefix_coeff_lt_of_mass (P : Nat[X]) (n B : Nat) (h : P.eval 1*n<B)
    (j : Nat) : (P*geomPoly n).coeff j<B := by
  apply (polynomial_coeff_le_mass _ j).trans_lt
  simpa [Polynomial.eval_mul, geomPoly_eval] using h

theorem directed_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (lo hi shift Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (haPc : ∀ j, aP.coeff j<2^1024) (haFc : ∀ j, aF.coeff j<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hlo : lo≤hi) (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024)
    (k : Nat) (hk : k<2048) :
    digit (2^1024)
      (directedFirst (aP.eval (2^1024),aF.eval (2^1024))
        (prefixes (bP.eval (2^1024)),prefixes (bF.eval (2^1024))) lo hi shift) k ≤
      (weightedHistogram
        (fun p : α×β => ga p.1 ∧ gb p.2 ∧ bb p.2≤ba p.1 ∧
          lo≤ba p.1-bb p.2 ∧ ba p.1-bb p.2≤hi)
        (fun p => ba p.1+shift) (fun p => wa p.1+wb p.2)).coeff k := by
  have da (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j=aP.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aP haPc
  have df (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j=aF.coeff j :=
    ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j aF haFc
  have hbp' (j : Nat) : bP.coeff j≤∑ b, if gb b ∧ bb b=j then 1 else 0 := by
    simpa only [weightedHistogram_coeff] using hbp j
  have hbf' (j : Nat) : bF.coeff j≤∑ b, if gb b ∧ bb b=j then wb b else 0 := by
    simpa only [weightedHistogram_coeff] using hbf j
  have hap' (j : Nat) : digit (2^1024) (aP.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then 1 else 0 := by
    rw [da]; simpa only [weightedHistogram_coeff] using hap j
  have haf' (j : Nat) : digit (2^1024) (aF.eval (2^1024)) j≤
      ∑ a, if ga a ∧ ba a=j then wa a else 0 := by
    rw [df]; simpa only [weightedHistogram_coeff] using haf j
  have wp := window_prefix_interval bP (prefix_coeff_lt_of_mass bP 2048 _ hbPm) lo hi
  have wf := window_prefix_interval bF (prefix_coeff_lt_of_mass bF 2048 _ hbFm) lo hi
  apply directed_histogram_lower ga gb ba wa bb wb _ _ bP.coeff bF.coeff lo hi shift
    haP haF ?_ (fun j hj => wp j hlo hj) (fun j hj => wf j hlo hj)
    hap' haf' hbp' hbf' k hk
  intro j hj
  dsimp only
  rw [wp j hlo hj, wf j hlo hj]
  by_cases hl : lo≤j
  · simp only [if_pos hl]
    exact directed_cross_small ga gb ba wa bb wb _ _ bP.coeff bF.coeff
      hap' haf' hbp' hbf' Ma Mb _ hwa hwb hsize j (Ico (j-hi) (j-lo+1))
  · simp only [if_neg hl, Nat.mul_zero, Nat.zero_add]
    positivity

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev binList : List Nat := 0 :: binPairs.map Prod.snd

theorem binList_length : binList.length = 11261 := by
  have h := congrArg List.length bin_indices_checked
  simp only [List.length_map, List.length_range'] at h
  simp only [binList, List.length_cons, List.length_map, h]

theorem binList_bound_checked : binList.all (fun b => decide (b<1024)) = true := by decide +kernel

theorem binList_bound (i : Fin binList.length) : binList[i]<1024 := by
  have h := List.all_eq_true.mp binList_bound_checked _ (List.getElem_mem i.isLt)
  exact of_decide_eq_true h

private theorem child_bounds (K : Nat) (hK : K ∈ [64,128]) : 1 ≤ K ∧ K ≤ 128 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  rcases hK with hK | hK <;> subst K <;> decide

theorem history_mass_small {β : Type} [Fintype β] (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21) :
    Fintype.card (Fin r.val → Fin K×β)<2^384 ∧
      Fintype.card (Fin r.val → Fin K×β)*(K*563)<2^384 := by
  rw [coordinate_history_card hβ K r.val]
  have hmass := coordinate_mass_small K r.val (child_bounds K hK).2 (by omega)
  refine ⟨?_,hmass⟩
  calc
    (K*563)^r.val = (K*563)^r.val*1 := (Nat.mul_one _).symm
    _ ≤ (K*563)^r.val*(K*563) := Nat.mul_le_mul_left _ (by have := (child_bounds K hK).1; omega)
    _ < 2^384 := hmass

/-- The concrete packed coordinate stores the two retained histograms exactly;
no arithmetic carry can cross the1024-bit bins. -/
theorem coordinate_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    coordinate K r.val =
      ((binnedPoly binList (coordinatePoly K r.val).coeff).eval (2^1024),
       (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval (2^1024)) := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_no_carry binList (coordinateCoverage val) (coordinatePoly K r.val) hp (K*563)
    (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
    (hm.2.trans_le (by decide +kernel))
  simpa only [coordinate, coordinatePacked_eval, binList] using h.1

theorem coordinate_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (binnedPoly binList (coordinatePoly K r.val).coeff)
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)) ∧
    CoeffLE (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j))
      (weightedHistogram (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)) :=
  coordinate_histograms_lower binList (coordinateCoverage val) (coordinatePoly K r.val) hp

theorem coordinate_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (binnedPoly binList (coordinatePoly K r.val).coeff).eval 1<2^384 ∧
    (binnedPoly binList (fun j => j*(coordinatePoly K r.val).coeff j)).eval 1<2^384 := by
  have h := coordinate_histograms_mass binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) (coordinate_coverage_le val hβ)
  have hm := history_mass_small hβ K hK r
  exact ⟨h.1.trans_lt hm.1,h.2.trans_lt hm.2⟩

theorem coordinate_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (coordinate K r.val).1<(2^1024)^1024 ∧ (coordinate K r.val).2<(2^1024)^1024 := by
  have hm := history_mass_small hβ K hK r
  have h := bucket_histogram_bounds binList (coordinateCoverage val) (coordinatePoly K r.val) hp
    (K*563) 1024 (coordinate_coverage_le val hβ) (hm.1.trans_le (by decide +kernel))
      (hm.2.trans_le (by decide +kernel)) binList_bound
  simpa only [coordinate, coordinatePacked_eval, binList] using h

end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathPacked
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def pieceValueWith
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length × Bool) : Nat :=
  if e.2 then
    if runs[e.1].2.1=0 then 0 else
      F b (P a.1,P a.2) (max 1 runs[e.1].1) runs[e.1].2.1 runs[e.1].2.2
  else F a (P b.1,P b.2) runs[e.1].1 runs[e.1].2.1 runs[e.1].2.2

theorem pieceValueWith_reverse
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length)
    (hz : runs[e].2.1≠0) :
    pieceValueWith F P runs a b (e,true) =
      F b (P a.1,P a.2) (max 1 runs[e].1) runs[e].2.1 runs[e].2.2 := by
  simp only [pieceValueWith, if_true, if_neg hz]

theorem pieceValueWith_forward
    (F : Cell → Cell → Nat → Nat → Nat → Nat) (P : Nat → Nat)
    (runs : List (Nat × Nat × Nat)) (a b : Cell) (e : Fin runs.length) :
    pieceValueWith F P runs a b (e,false) =
      F a (P b.1,P b.2) runs[e].1 runs[e].2.1 runs[e].2.2 := rfl

theorem addPieceValue_model (a b : Cell) (e : AddPiece) :
    addPieceValue a b e=pieceValueWith directedFirst prefixes addRuns a b e := rfl

theorem addPieceValue_forward (a b : Cell) (e : Fin addRuns.length) :
    addPieceValue a b (e,false) =
      directedFirst a (prefixes b.1,prefixes b.2)
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,false)).trans
    (pieceValueWith_forward directedFirst prefixes addRuns a b e)

theorem addPieceValue_reverse (a b : Cell) (e : Fin addRuns.length)
    (hz : addRuns[e].2.1≠0) :
    addPieceValue a b (e,true) =
      directedFirst b (prefixes a.1,prefixes a.2)
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 :=
  (addPieceValue_model a b (e,true)).trans
    (pieceValueWith_reverse directedFirst prefixes addRuns a b e hz)

theorem histogram_reverse {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) (gb : β → Prop)
    (ba wa : α → Nat) (bb wb : β → Nat) (lo hi shift : Nat) :
    weightedHistogram
      (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
        max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
      (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2) =
    weightedHistogram
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
      (fun p => bb p.2+shift) (fun p => wa p.1+wb p.2) := by
  classical
  have he := weightedHistogram_equiv (Equiv.prodComm α β)
    (fun p : β×α => gb p.1 ∧ ga p.2 ∧ ba p.2≤bb p.1 ∧
      max 1 lo≤bb p.1-ba p.2 ∧ bb p.1-ba p.2≤hi)
    (fun p => bb p.1+shift) (fun p => wb p.1+wa p.2)
  have hg : (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
      max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) =
      (fun p : α×β => ga p.1 ∧ gb p.2 ∧ ba p.1<bb p.2 ∧
        lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi) := by
    funext p
    apply propext
    constructor
    · rintro ⟨hb,ha,hle,hlo,hhi⟩
      exact ⟨ha,hb,by omega,by omega,hhi⟩
    · rintro ⟨ha,hb,hlt,hlo,hhi⟩
      exact ⟨hb,ha,by omega,by omega,hhi⟩
  calc _ = _ := he.symm
       _ = _ := by
        change weightedHistogram
          (fun p : α×β => gb p.2 ∧ ga p.1 ∧ ba p.1≤bb p.2 ∧
            max 1 lo≤bb p.2-ba p.1 ∧ bb p.2-ba p.1≤hi)
          (fun p => bb p.2+shift) (fun p => wb p.2+wa p.1) = _
        rw [hg]
        congr 1
        funext p
        exact Nat.add_comm _ _

theorem addFirst_polynomial_histogram_lower {α β : Type} [Fintype α] [Fintype β]
    (ga : α → Prop) [DecidablePred ga] (gb : β → Prop) [DecidablePred gb]
    (ba wa : α → Nat) (bb wb : β → Nat)
    (aP aF bP bF : Nat[X]) (Ma Mb : Nat)
    (haP : aP.eval (2^1024)<(2^1024)^2048)
    (haF : aF.eval (2^1024)<(2^1024)^2048)
    (hbP : bP.eval (2^1024)<(2^1024)^2048)
    (hbF : bF.eval (2^1024)<(2^1024)^2048)
    (haPm : aP.eval 1*2048<2^1024) (haFm : aF.eval 1*2048<2^1024)
    (hbPm : bP.eval 1*2048<2^1024) (hbFm : bF.eval 1*2048<2^1024)
    (hap : CoeffLE aP (weightedHistogram ga ba (fun _ => 1)))
    (haf : CoeffLE aF (weightedHistogram ga ba wa))
    (hbp : CoeffLE bP (weightedHistogram gb bb (fun _ => 1)))
    (hbf : CoeffLE bF (weightedHistogram gb bb wb))
    (hwa : ∀ a, wa a≤Ma) (hwb : ∀ b, wb b≤Mb)
    (hsize : Fintype.card α*Fintype.card β*(Ma+Mb)<2^1024) :
    addFirst (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024))<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024)
        (addFirst (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024))) j≤
        (weightedHistogram (fun p : α×β => ga p.1 ∧ gb p.2)
          (fun p => mergeBin (ba p.1) (bb p.2)) (fun p => wa p.1+wb p.2)).coeff j := by
  classical
  have coeff (P : Nat[X]) (h : P.eval 1*2048<2^1024) (j : Nat) : P.coeff j<2^1024 := by
    have hc := polynomial_coeff_le_mass P j
    omega
  apply addFirst_histogram_lower ga gb ba wa bb wb _ _ Ma Mb hwa hwb hsize
  intro e k hk
  rcases e with ⟨e,b⟩
  cases b
  · apply (congrArg (fun x => digit (2^1024) x k)
      (addPieceValue_forward (aP.eval (2^1024),aF.eval (2^1024))
        (bP.eval (2^1024),bF.eval (2^1024)) e)).le.trans
    exact directed_polynomial_histogram_lower ga gb ba wa bb wb aP aF bP bF
      addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2 Ma Mb
      haP haF (coeff aP haPm) (coeff aF haFm) hbPm hbFm hap haf hbp hbf
      (add_run_bounds e).1 hwa hwb hsize k hk
  · by_cases hz : addRuns[e].2.1=0
    · simp only [addPieceValue, if_true, hz, digit, Nat.zero_div, Nat.zero_mod]
      exact Nat.zero_le _
    · have hlo : max 1 addRuns[e].1≤addRuns[e].2.1 := by
        have h := (add_run_bounds e).1
        omega
      have hs : Fintype.card β*Fintype.card α*(Mb+Ma)<2^1024 := by
        simpa only [Nat.mul_comm, Nat.add_comm] using hsize
      have h := directed_polynomial_histogram_lower gb ga bb wb ba wa bP bF aP aF
        (max 1 addRuns[e].1) addRuns[e].2.1 addRuns[e].2.2 Mb Ma
        hbP hbF (coeff bP hbPm) (coeff bF hbFm) haPm haFm hbp hbf hap haf
        hlo hwb hwa hs k hk
      have he' := histogram_reverse ga gb ba wa bb wb
        addRuns[e].1 addRuns[e].2.1 addRuns[e].2.2
      have hh := h.trans_eq (congrArg (fun P : Nat[X] => P.coeff k) he')
      exact (congrArg (fun x => digit (2^1024) x k)
        (addPieceValue_reverse (aP.eval (2^1024),aF.eval (2^1024))
          (bP.eval (2^1024),bF.eval (2^1024)) e hz)).le.trans hh

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathCoordinate
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

noncomputable abbrev probPoly (K r : Nat) : Nat[X] := binnedPoly binList (coordinatePoly K r).coeff
noncomputable abbrev firstPoly (K r : Nat) : Nat[X] :=
  binnedPoly binList (fun j => j*(coordinatePoly K r).coeff j)

attribute [local irreducible] binnedPoly coordinatePoly

noncomputable def coordinateGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Prop := coordinateCoverage val h<binList.length
noncomputable def coordinateBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : Fin r → Fin K×β) : Nat := binList[coordinateCoverage val h]?.getD 0

abbrev BranchHistory (β : Type) (K r : Nat) :=
  (Fin r → Fin K×β) × (Fin r → Fin K×β)
noncomputable def branchGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Prop :=
  coordinateGood val h.1 ∧ coordinateGood val h.2
noncomputable def branchBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat := coordinateBin val h.1+coordinateBin val h.2
noncomputable def branchCoverage {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (h : BranchHistory β K r) : Nat :=
  coordinateCoverage val h.1*coordinateCoverage val h.2

theorem branch_bin_bound {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) {K r : Nat} (h : BranchHistory β K r)
    (hg : branchGood val h) : branchBin val h<2047 := by
  have hb (a : Fin r → Fin K×β) (ha : coordinateGood val a) : coordinateBin val a<1024 := by
    unfold coordinateGood at ha
    unfold coordinateBin
    rw [List.getElem?_eq_getElem ha]
    exact binList_bound ⟨coordinateCoverage val a,ha⟩
  have h1 := hb h.1 hg.1
  have h2 := hb h.2 hg.2
  unfold branchBin
  omega

theorem branch_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE ((probPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (fun _ : BranchHistory β K r.val => 1)) ∧
    CoeffLE ((firstPoly K r.val)^2) (weightedHistogram (branchGood val)
      (branchBin val) (branchCoverage (K:=K) (r:=r.val) val)) := by
  have h := coordinate_histogram val hβ K hK r hp
  unfold probPoly firstPoly branchGood branchBin branchCoverage coordinateGood coordinateBin
  constructor
  · simpa only [pow_two, probPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      Nat.one_mul] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (fun _ => 1)
        _ _ h.1 h.1
  · simpa only [pow_two, firstPoly, branchGood, coordinateGood, branchBin, coordinateBin,
      branchCoverage] using weightedHistogram_product_lower
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E : Fin r.val → Fin K×β => coordinateCoverage val E<binList.length)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        (fun E => binList[coordinateCoverage val E]?.getD 0) (coordinateCoverage val)
        _ _ h.2 h.2

theorem product_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.product (coordinate K r.val) =
      (((probPoly K r.val)^2).eval (2^1024), ((firstPoly K r.val)^2).eval (2^1024)) := by
  rw [coordinate_polynomial val hβ K hK r hp]
  simp only [SharedPathPacked.product, Polynomial.eval_pow, probPoly, firstPoly]

theorem square_mass (a : Nat) (ha : a<2^384) : a^2*2048<2^1024 := by
  have h : a^2≤(2^384)^2 := Nat.pow_le_pow_left ha.le 2
  exact lt_of_le_of_lt (Nat.mul_le_mul_right 2048 h) (by decide +kernel)

theorem product_mass {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ((probPoly K r.val)^2).eval 1*2048<2^1024 ∧
      ((firstPoly K r.val)^2).eval 1*2048<2^1024 := by
  have hm := coordinate_mass val hβ K hK r hp
  simpa only [Polynomial.eval_pow, probPoly, firstPoly] using
    And.intro (square_mass _ hm.1) (square_mass _ hm.2)

theorem product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K ∈ [64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate K r.val)).1<(2^1024)^2048 ∧
      (SharedPathPacked.product (coordinate K r.val)).2<(2^1024)^2048 := by
  have hm := coordinate_size val hβ K hK r hp
  have hs (a : Nat) (ha : a<(2^1024)^1024) : a^2<(2^1024)^2048 := by
    have h := Nat.pow_lt_pow_left ha (by decide : 2≠0)
    simpa only [← pow_mul] using h
  exact ⟨hs _ hm.1,hs _ hm.2⟩

theorem split_product_size {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (SharedPathPacked.product (coordinate 64 t)).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 t)).2<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).1<(2^1024)^2048 ∧
    (SharedPathPacked.product (coordinate 64 (r-t))).2<(2^1024)^2048 := by
  have h1 := product_size val hβ 64 (by simp) (⟨t,by omega⟩ : Fin 21) (hp t ht)
  have h2 := product_size val hβ 64 (by simp) (⟨r-t,by omega⟩ : Fin 21) (hp (r-t) (Nat.sub_le ..))
  exact ⟨h1.1,h1.2,h2.1,h2.2⟩

open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem branch_coverage_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    {K r : Nat} (h : BranchHistory β K r) : branchCoverage val h≤(K*563)^2 := by
  exact (Nat.mul_le_mul (coordinate_coverage_le val hβ h.1)
    (coordinate_coverage_le val hβ h.2)).trans_eq (pow_two _).symm

theorem split_branch_mass {β : Type} [Fintype β]
    (hβ : Fintype.card β=563) (r t : Nat) (hr : r≤20) (ht : t≤r) :
    Fintype.card (BranchHistory β 64 t)*Fintype.card (BranchHistory β 64 (r-t))*
      ((64*563)^2+(64*563)^2)<2^1024 := by
  simp only [BranchHistory, Fintype.card_prod, coordinate_history_card hβ]
  have he : (64*563)^t*(64*563)^t*((64*563)^(r-t)*(64*563)^(r-t)) =
      ((64*563)^r)^2 := by
    calc
      _ = ((64*563)^t*(64*563)^(r-t))^2 := by ring
      _ = _ := by rw [← pow_add, Nat.add_sub_of_le ht]
  rw [he]
  have hs : ((64*563)^r)^2*((64*563)^2+(64*563)^2) =
      ((64*563)^r*(64*563))^2*2 := by ring
  rw [hs]
  have hmass := coordinate_mass_small 64 r (by decide) hr
  have h := square_mass _ hmass
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (by decide : 2≤2048)) h

end ClaudeWCT.Numerics.SharedPathCoordinate


namespace ClaudeWCT.Numerics.SharedPathList
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def runsCoverCheck : List (Nat × Nat × Nat) → Nat → Nat → Bool
  | [], start, finish => decide (start=finish)
  | e::es, start, finish => decide (e.1=start ∧ start≤e.2.1) &&
      runsCoverCheck es (e.2.1+1) finish

theorem runsCoverCheck_sound (runs : List (Nat × Nat × Nat)) (start finish d : Nat)
    (h : runsCoverCheck runs start finish=true) (hd : start≤d ∧ d<finish) :
    ∃ e ∈ runs, e.1≤d ∧ d≤e.2.1 := by
  induction runs generalizing start with
  | nil => simp only [runsCoverCheck, decide_eq_true_eq] at h; omega
  | cons e es ih =>
    simp only [runsCoverCheck, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases he : d≤e.2.1
    · exact ⟨e,List.mem_cons_self,by omega,he⟩
    · obtain ⟨v,hv,hvd⟩ := ih (e.2.1+1) h.2 (by omega)
      exact ⟨v,List.mem_cons_of_mem _ hv,hvd⟩

theorem add_runs_contiguous : runsCoverCheck addRuns 0 2047=true := by decide +kernel

theorem add_runs_cover_checked (d : Fin 2047) : ∃ e : Fin addRuns.length,
    addRuns[e].1 ≤ d.val ∧ d.val ≤ addRuns[e].2.1 := by
  obtain ⟨v,hv,hd⟩ := runsCoverCheck_sound addRuns 0 2047 d.val
    add_runs_contiguous ⟨Nat.zero_le _,d.isLt⟩
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hv
  refine ⟨i,?_⟩
  simpa only [←hi, List.get_eq_getElem, Fin.getElem_fin] using hd

theorem mergeBin_interval_of_lt (i j : Nat) (hi : i<2047) (hj : j<2047) :
    (101/100 : ℝ)^(mergeBin i j)*(100/101) ≤ (101/100 : ℝ)^i+(101/100 : ℝ)^j ∧
      (101/100 : ℝ)^i+(101/100 : ℝ)^j ≤ (101/100 : ℝ)^(mergeBin i j) := by
  rcases le_total j i with hji|hij
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨i-j,by omega⟩
    exact mergeBin_interval e i j hji hlo hhi
  · obtain ⟨e,hlo,hhi⟩ := add_runs_cover_checked ⟨j-i,by omega⟩
    have h := mergeBin_interval e j i hij hlo hhi
    simpa only [mergeBin_comm j i, add_comm] using h

theorem RoundedInterval.merge {a i j : Nat} {x y : ℝ}
    (hx : RoundedInterval a i x) (hy : RoundedInterval a j y)
    (hi : i<2047) (hj : j<2047) :
    RoundedInterval (a+1) (mergeBin i j) (x+y) := by
  have h := mergeBin_interval_of_lt i j hi hj
  exact hx.add hy h.1 h.2

end ClaudeWCT.Numerics.SharedPathList


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def reverseFeePoly (n : Nat) (f : Nat → Nat) : Nat[X] :=
  ∑ i ∈ range n, C (f i)*X^(n-1-i)

theorem reverseFeePoly_eval_one (n : Nat) (f : Nat → Nat) :
    (reverseFeePoly n f).eval 1=∑ i ∈ range n, f i := by
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, one_pow, mul_one]

theorem reverseFeePoly_dot (P : Nat[X]) (n : Nat) (f : Nat → Nat) :
    (P*reverseFeePoly n f).coeff (n-1)=∑ i ∈ range n, P.coeff i*f i := by
  simp only [reverseFeePoly, Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [←mul_assoc, Polynomial.coeff_mul_X_pow', if_pos (by omega),
    show n-1-(n-1-i)=i by omega, Polynomial.coeff_mul_C]

theorem packed_convolution_dot (P : Nat[X]) (B n : Nat) (f : Nat → Nat)
    (hB : 0<B) (hmass : P.eval 1*(∑ i ∈ range n, f i)<B) :
    (P.eval B*(reverseFeePoly n f).eval B/B^(n-1))%B =
      ∑ i ∈ range n, P.coeff i*f i := by
  have hc (i : Nat) : (P*reverseFeePoly n f).coeff i<B := by
    have h := ClaudeWCT.Numerics.N600.sum_coeff_le_eval_one (P*reverseFeePoly n f) {i}
    simp only [Finset.sum_singleton, Polynomial.eval_mul, reverseFeePoly_eval_one] at h
    exact h.trans_lt hmass
  rw [←Polynomial.eval_mul]
  exact (ClaudeWCT.Numerics.eval_div_pow_mod hB (n-1) (P*reverseFeePoly n f) hc).trans
    (reverseFeePoly_dot P n f)

end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def splitGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Prop :=
  if t=0 then branchGood val h.2 else if u=0 then branchGood val h.1 else
    branchGood val h.1 ∧ branchGood val h.2
noncomputable def splitBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  if t=0 then branchBin val h.2 else if u=0 then branchBin val h.1 else
    mergeBin (branchBin val h.1) (branchBin val h.2)
noncomputable def splitWeight {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (h : BranchHistory β 64 t × BranchHistory β 64 u) : Nat :=
  branchCoverage val h.1+branchCoverage val h.2

def splitRow (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coordinate 64 t)
  let b := SharedPathPacked.product (coordinate 64 (r-t))
  if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def pairGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Prop :=
  splitGood val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))
noncomputable def pairBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : PairHistory β r) : Nat :=
  splitBin val (occ h.1 0) (occ h.1 1)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1))

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem coordinate_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : Fin 0 → Fin K×β) : coordinateCoverage val h=0 := by
  classical
  unfold coordinateCoverage
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp ha).2 (0 : Fin 6)
  exact Fin.elim0 i

theorem branch_empty {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (K : Nat) (h : BranchHistory β K 0) : branchCoverage val h=0 := by
  simp only [branchCoverage, coordinate_empty, Nat.zero_mul]

theorem coordinate_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : Fin r → Fin K×β) (hg : coordinateGood val h) :
    RoundedInterval 1 (coordinateBin val h) (coordinateCoverage val h : ℝ) := by
  have hpos := coordinate_coverage_pos val hr h
  have hlen : coordinateCoverage val h≤11260 := by
    unfold coordinateGood at hg
    rw [binList_length] at hg
    omega
  have hb := bin_lookup_bounds bin_runs_checked bin_indices_checked
    (coordinateCoverage val h) (by omega) hlen
  have he : bins[coordinateCoverage val h]?.getD 0=coordinateBin val h := by
    simp only [bins, coordinateBin, binList, List.getElem?_toArray]
  rw [he] at hb
  have hi := geometric_bin_interval _ _ hb.1 hb.2
  exact ⟨by positivity,by simpa only [pow_one,mul_comm] using hi.1,hi.2⟩

theorem branch_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {K r : Nat} (hr : 0<r) (h : BranchHistory β K r) (hg : branchGood val h) :
    RoundedInterval 2 (branchBin val h) (branchCoverage val h : ℝ) := by
  have h1 := coordinate_interval val hr h.1 hg.1
  have h2 := coordinate_interval val hr h.2 hg.2
  simpa only [branchBin, branchCoverage, Nat.cast_mul] using h1.mul h2

theorem interval_weaken {a b i : Nat} {x : ℝ}
    (h : RoundedInterval a i x) (hab : a≤b) : RoundedInterval b i x := by
  refine ⟨h.nonneg,?_,h.upper⟩
  apply le_trans ?_ h.lower
  apply mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hab

theorem split_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    (t u : Nat) (hpos : 0<t+u) (h : BranchHistory β 64 t × BranchHistory β 64 u)
    (hg : splitGood val t u h) :
    RoundedInterval 3 (splitBin val t u h) (splitWeight val t u h : ℝ) := by
  by_cases ht : t=0
  · subst t
    have hu : 0<u := by omega
    have hI := interval_weaken (branch_interval val hu h.2 (by simpa only [splitGood,ite_true] using hg)) (by decide : 2≤3)
    simpa only [splitBin,splitWeight,ite_true,branch_empty,Nat.zero_add] using hI
  · by_cases hu : u=0
    · subst u
      have ht' : 0<t := by omega
      have hI := interval_weaken (branch_interval val ht' h.1 (by simpa only [splitGood,if_neg ht,ite_true] using hg)) (by decide : 2≤3)
      simpa only [splitBin,splitWeight,if_neg ht,ite_true,branch_empty,Nat.add_zero] using hI
    · have hg' : branchGood val h.1 ∧ branchGood val h.2 := by
        simpa only [splitGood,if_neg ht,if_neg hu] using hg
      have h1 := branch_interval val (by omega : 0<t) h.1 hg'.1
      have h2 := branch_interval val (by omega : 0<u) h.2 hg'.2
      have hI := h1.merge h2 (branch_bin_bound val h.1 hg'.1) (branch_bin_bound val h.2 hg'.2)
      simpa only [splitBin,splitWeight,if_neg ht,if_neg hu,Nat.cast_add] using hI

theorem pair_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : PairHistory β r) (hg : pairGood val h) :
    RoundedInterval 3 (pairBin val h) (pairCoverage val h : ℝ) := by
  have hs : occ h.1 0+occ h.1 1=r := by
    simpa only [Fin.sum_univ_two] using occ_sum h.1
  exact split_interval val _ _ (by omega)
    ((splitRanks h.1 h.2.1 0,splitRanks h.1 h.2.2 0),
     (splitRanks h.1 h.2.1 1,splitRanks h.1 h.2.2 1)) hg

end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathCoordinate
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

private theorem histogram_left_unique_lower {α β : Type} [Fintype α] [Unique α] [Fintype β]
    (g : β → Prop) (b w : β → Nat) (v : α → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.2) (fun p => b p.2) (fun p => v p.1+w p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

private theorem histogram_right_unique_lower {α β : Type} [Fintype α] [Fintype β] [Unique β]
    (g : α → Prop) (b w : α → Nat) (v : β → Nat) :
    CoeffLE (weightedHistogram g b w)
      (weightedHistogram (fun p : α×β => g p.1) (fun p => b p.1) (fun p => w p.1+v p.2)) := by
  classical
  intro j
  rw [weightedHistogram_coeff, weightedHistogram_coeff, Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> omega

theorem product_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (SharedPathPacked.product (coordinate K r.val)).2 j =
      ((firstPoly K r.val)^2).coeff j := by
  rw [product_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (product_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass ((firstPoly K r.val)^2) i
    omega)

theorem split_row_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r t : Nat) (hr : r≤20) (ht : t≤r)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    splitRow r t<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (splitRow r t) j ≤
        (weightedHistogram (splitGood val t (r-t)) (splitBin val t (r-t))
          (splitWeight val t (r-t))).coeff j := by
  classical
  have hsize := split_product_size val hβ r t hr ht hp
  have ht' : t<21 := by omega
  have hu' : r-t<21 := by omega
  have hPt := branch_histogram val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
  have hPu := branch_histogram val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
  letI : Unique (BranchHistory β 64 0) := {
    default := (Fin.elim0, Fin.elim0)
    uniq := by intro x; apply Prod.ext <;> funext i <;> exact Fin.elim0 i }
  unfold splitGood splitBin splitWeight
  by_cases h0 : t=0
  · subst t
    simp only [splitRow, if_pos rfl, Nat.sub_zero, ite_true]
    refine ⟨hsize.2.2.2,?_⟩
    intro j hj
    rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
    apply (hPu.2 j).trans
    simpa only [splitGood, splitBin, splitWeight, if_pos rfl, Nat.sub_zero, ite_true] using
      histogram_left_unique_lower (α:=BranchHistory β 64 0)
        (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
        (branchCoverage val) j
  · by_cases h1 : r-t=0
    · have htr : t=r := by omega
      subst t
      letI : Unique (BranchHistory β 64 (r-r)) := by
        simpa only [Nat.sub_self] using (inferInstance : Unique (BranchHistory β 64 0))
      simp only [splitRow, if_neg h0, Nat.sub_self, if_pos rfl, ite_true]
      refine ⟨hsize.2.1,?_⟩
      intro j hj
      rw [product_first_digit val hβ 64 (by simp) (⟨r,by omega⟩ : Fin 21) (hp r le_rfl)]
      apply (hPt.2 j).trans
      simpa only [splitGood, splitBin, splitWeight, if_neg h0, Nat.sub_self, if_pos rfl, ite_true] using
        histogram_right_unique_lower (β:=BranchHistory β 64 (r-r))
          (branchGood (K:=64) (r:=r) val) (branchBin val) (branchCoverage val)
          (branchCoverage val) j
    · have hmt := product_mass val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hmu := product_mass val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      have hEt := product_polynomial val hβ 64 (by simp) (⟨t,ht'⟩ : Fin 21) (hp t ht)
      have hEu := product_polynomial val hβ 64 (by simp) (⟨r-t,hu'⟩ : Fin 21) (hp _ (Nat.sub_le ..))
      rw [hEt,hEu] at hsize
      have h := addFirst_polynomial_histogram_lower
        (branchGood (K:=64) (r:=t) val) (branchGood (K:=64) (r:=r-t) val)
        (branchBin val) (branchCoverage val) (branchBin val) (branchCoverage val)
        ((probPoly 64 t)^2) ((firstPoly 64 t)^2) ((probPoly 64 (r-t))^2) ((firstPoly 64 (r-t))^2)
        ((64*563)^2) ((64*563)^2)
        hsize.1 hsize.2.1 hsize.2.2.1 hsize.2.2.2 hmt.1 hmt.2 hmu.1 hmu.2
        hPt.1 hPt.2 hPu.1 hPu.2
        (branch_coverage_le val hβ) (branch_coverage_le val hβ) (split_branch_mass hβ r t hr ht)
      simpa only [splitRow, if_neg h0, if_neg h1, hEt, hEu, splitGood, splitBin, splitWeight, ite_true] using h

end ClaudeWCT.Numerics.SharedPathPair


namespace ClaudeWCT.Numerics.SharedPathPair
open Finset Polynomial
open ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedPathReflection ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedDigitBlock
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

theorem pair_histogram_split {β : Type} [Fintype β] (val : β → Fin 6 → Nat) (r : Nat) :
    weightedHistogram (pairGood (r:=r) val) (pairBin val) (pairCoverage val) =
      ∑ t ∈ range (r+1), r.choose t • weightedHistogram (splitGood val t (r-t))
        (splitBin val t (r-t)) (splitWeight val t (r-t)) := by
  exact weightedHistogram_selector_split r
    (fun t u A B C D => splitGood val t u ((A,B),(C,D)))
    (fun t u A B C D => splitBin val t u ((A,B),(C,D)))
    (fun t u A B C D => splitWeight val t u ((A,B),(C,D)))

private theorem range_map_sum (n : Nat) (f : Nat → Nat) :
    ((List.range n).map f).sum = ∑ t ∈ range n, f t := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, ih, Finset.sum_range_succ]

theorem pairFirst_sum (r : Nat) :
    pairFirst r = ∑ t ∈ range (r+1), r.choose t * splitRow r t := by
  classical
  unfold pairFirst
  rw [foldl_weighted_sum, Nat.zero_add, range_map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have htr : t≤r := by have h := Finset.mem_range.mp ht; omega
  have ht' : t<r+1 := by omega
  have hu' : r-t<r+1 := by omega
  have get (u : Nat) (hu : u<r+1) :
      ((List.range (r+1)).map fun t => SharedPathPacked.product (coordinate 64 t)).getD u (0,0) =
        SharedPathPacked.product (coordinate 64 u) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hu)]
    simp only [List.getElem_map, List.getElem_range]
  rw [get t ht', get (r-t) hu']
  rw [PoissonReflect.fact_eq, PoissonReflect.fact_eq, PoissonReflect.fact_eq, ← Nat.choose_eq_factorial_div_factorial htr]
  rfl

private theorem eval_nsmul_nat (P : Nat[X]) (n B : Nat) :
    (n • P).eval B=n*P.eval B := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.eval_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.eval_add,ih,Nat.succ_mul]

private theorem coeff_nsmul_nat (P : Nat[X]) (n j : Nat) :
    (n • P).coeff j=n*P.coeff j := by
  induction n with
  | zero => simp only [zero_nsmul,Polynomial.coeff_zero,Nat.zero_mul]
  | succ n ih => rw [succ_nsmul,Polynomial.coeff_add,ih,Nat.succ_mul]

noncomputable def pairPoly (r : Nat) : Nat[X] :=
  ∑ t ∈ range (r+1), r.choose t • packedPoly (2^1024) 2048 (splitRow r t)

theorem pair_polynomial {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    (pairPoly r).eval (2^1024)=pairFirst r ∧
      CoeffLE (pairPoly r) (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)) := by
  classical
  constructor
  · rw [pairFirst_sum]
    unfold pairPoly
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [eval_nsmul_nat,
      packedPoly_eval _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).1]
  · rw [pair_histogram_split]
    intro j
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat]
    apply Finset.sum_le_sum
    intro t ht
    exact Nat.mul_le_mul_left _
      (packedPoly_below _ _ _ _ (split_row_histogram val hβ r t hr (Nat.le_of_lt_succ (Finset.mem_range.mp ht)) hp).2 j)

theorem pairFirst_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ u, u≤r → ∀ j, (coordinatePoly 64 u).coeff j ≤
      (univ.filter fun E : Fin u → Fin 64×β => coordinateCoverage val E=j).card) :
    pairFirst r<(2^1024)^2048 ∧
      ∀ j, j<2048 → digit (2^1024) (pairFirst r) j ≤
        (weightedHistogram (pairGood val) (pairBin val) (pairCoverage (r:=r) val)).coeff j := by
  classical
  have h := pair_polynomial val hβ r hr hp
  have hc (j : Nat) : (pairPoly r).coeff j<2^1024 := by
    apply histogram_lower_coeff_lt _ _ _ _ h.2 (2*(64*563)^2) _
    · intro a _
      exact pair_coverage_le val hβ a
    · rw [pair_history_card hβ]
      exact pair_mass_small r hr
  have hz (j : Nat) (hj : 2048≤j) : (pairPoly r).coeff j=0 := by
    simp only [pairPoly, Polynomial.finsetSum_coeff, coeff_nsmul_nat, packedPoly,
      polyOf_coeff, if_neg (by omega : ¬j<2048), Nat.mul_zero, Finset.sum_const_zero]
  rw [←h.1]
  refine ⟨polynomial_eval_lt _ _ _ (by positivity) (fun j _ => hc j) hz,?_⟩
  intro j hj
  rw [digit_polynomial_eval _ _ _ (by positivity) (fun i _ => hc i) hz j hj]
  exact h.2 j

end ClaudeWCT.Numerics.SharedPathPair

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] feeRuns feeEntries fees scale maxFee

theorem fees_bound_of_chunks (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210) (i : Nat) (hi : i < 7210) :
    (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale :=  by
  have hv :=  fee_run_values hsize hchunks
  obtain ⟨e,he,_,_,hfee⟩ :=  fee_lookup_run (fun e he  => (hv e he).1) hidx i hi
  rw [hfee]
  exact (hv e he).2.2

theorem histogram_winsor_pair {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = total)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1))  ≤ 
      κ/(scale : ℝ)*(((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
        maxFee*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ℝ) ∧
    (∑ a, max 0 (κ*(weight a : ℝ)-6/5))  ≤ 
      κ/(scale : ℝ)*(((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
        scale*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ℝ) :=  by
  have hS : (0 : ℝ) < scale :=  by exact_mod_cast scale_pos
  have hnon (a : α) : 0 ≤ κ*(weight a : ℝ) :=  mul_nonneg hκ (Nat.cast_nonneg _)
  have hfee :=  fees_bound_of_chunks hsize hchunks hidx
  have hlocal (a : α) (ha : good a) (hb : bin a < 7210) := 
    fee_lookup_sound hsize hchunks hidx (bin a) hb (κ*(weight a : ℝ))
      (hnon a) (hinterval a ha).1 (hinterval a ha).2
  constructor
  · apply histogram_moment_bound 7210 total maxFee good bin weight P hP htotal
      (fun a  => Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)
      (fun j  => (fees[j]?.getD (0,0)).1) (κ/scale) (div_nonneg hκ hS.le)
      (fun j hj  => (hfee j hj).1)
    · intro a
      convert global_fee_sound (κ*(weight a : ℝ)) (hnon a) using 1  <;> ring
    · intro a ha hb
      convert (hlocal a ha hb).1 using 1  <;> ring
  · apply histogram_moment_bound 7210 total scale good bin weight P hP htotal
      (fun a  => max 0 (κ*(weight a : ℝ)-6/5))
      (fun j  => (fees[j]?.getD (0,0)).2) (κ/scale) (div_nonneg hκ hS.le)
      (fun j hj  => (hfee j hj).2)
    · intro a
      have h : max 0 (κ*(weight a : ℝ)-6/5) ≤ κ*(weight a : ℝ) := 
        max_le (hnon a) (by linarith)
      convert h using 1
      field_simp
    · intro a ha hb
      convert (hlocal a ha hb).2 using 1  <;> ring

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

noncomputable def encodedForestPoly (p q : Nat) : Nat[X] :=
  (packedPoly (2^1024) 2048 p)^4 * packedPoly (2^1024) 1024 q

theorem encodedForest_encoding (p q : Nat)
    (hp : p < (2^1024)^2048) (hq : q < (2^1024)^1024) :
    (SharedPathPacked.spread 11 p)^4*SharedPathPacked.spread 10 q =
      (encodedForestPoly p q).eval (2^4096) :=
  SharedPathPacked.forest_packed_polynomial p q hp hq

theorem encodedForest_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r p q : Nat)
    (gp : PairHistory β r → Prop) [DecidablePred gp] (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) [DecidablePred gq]
    (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ j, j < 2048 → digit (2^1024) p j ≤
      (weightedHistogram gp bp (pairCoverage val)).coeff j)
    (hq : ∀ j, j < 1024 → digit (2^1024) q j ≤
      (weightedHistogram gq bq (coordinateCoverage val)).coeff j) :
    CoeffLE (encodedForestPoly p q)
      (weightedHistogram (fun h : ForestHistory β r => (∀ i, gp (h.1 i)) ∧ gq h.2)
        (fun h => (∑ i, bp (h.1 i))+bq h.2) (forestCoverage val)) := by
  exact forest_histogram_lower val r gp bp gq bq _ _
    (packedPoly_below _ _ _ _ hp) (packedPoly_below _ _ _ _ hq)

theorem encodedForest_coeff_small {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β = 563) (r p q : Nat) (hr : r ≤ 20)
    (gp : PairHistory β r → Prop) [DecidablePred gp] (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) [DecidablePred gq]
    (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ j, j < 2048 → digit (2^1024) p j ≤
      (weightedHistogram gp bp (pairCoverage val)).coeff j)
    (hq : ∀ j, j < 1024 → digit (2^1024) q j ≤
      (weightedHistogram gq bq (coordinateCoverage val)).coeff j)
    (j : Nat) : (encodedForestPoly p q).coeff j < 2^4096 := by
  have h := encodedForest_histogram val r p q gp bp gq bq hp hq
  refine histogram_lower_coeff_lt _ _ _ _ h alphabetSize (2^4096)
    (fun h _ => forest_coverage_le val hβ h) ?_ j
  rw [forest_history_card hβ r]
  exact forest_mass_small r hr

theorem forest_interval {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (gp : PairHistory β r → Prop) (bp : PairHistory β r → Nat)
    (gq : (Fin r → Fin 128×β) → Prop) (bq : (Fin r → Fin 128×β) → Nat)
    (hp : ∀ h, gp h → RoundedInterval 3 (bp h) (pairCoverage val h : ℝ))
    (hq : ∀ h, gq h → RoundedInterval 1 (bq h) (coordinateCoverage val h : ℝ))
    (h : ForestHistory β r) (hg : (∀ i, gp (h.1 i)) ∧ gq h.2) :
    RoundedInterval 13 ((∑ i, bp (h.1 i))+bq h.2) (forestCoverage val h : ℝ) := by
  have hf := RoundedInterval.forest (fun i => bp (h.1 i))
    (fun i => (pairCoverage val (h.1 i) : ℝ)) (bq h.2) (coordinateCoverage val h.2 : ℝ)
    (fun i => hp _ (hg.1 i)) (hq _ hg.2)
  simpa only [forestCoverage, Nat.cast_mul, Nat.cast_prod] using hf

end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] feeRuns feeEntries fees scale maxFee

theorem ofReal_sum_nat_bound {α : Type} [Fintype α]
    (f : α → ℝ) (κ : ℝ) (A B : Nat) (hκ : 0 ≤ κ) (hB : 0 < B)
    (hf : ∀ a, 0 ≤ f a) (h : (∑ a, f a) ≤ κ/(B : ℝ)*(A : ℝ)) :
    (∑ a, ENNReal.ofReal (f a)) ≤ ENNReal.ofReal κ/(B : ENNReal)*(A : ENNReal) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hf a)]
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  calc
    _ ≤ ENNReal.ofReal (κ/(B : ℝ)*(A : ℝ)) := ENNReal.ofReal_le_ofReal h
    _ = _ := by
      rw [ENNReal.ofReal_mul (div_nonneg hκ hBR.le), ENNReal.ofReal_div_of_pos hBR,
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

theorem histogram_winsor_pair_ennreal {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (P : Nat[X]) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = total)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hidx : feeEntries.map Prod.fst = List.range 7210)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*
        (((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
          maxFee*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*
        (((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
          scale*(total-∑ j ∈ range 7210, P.coeff j) : Nat) : ENNReal) := by
  have h := histogram_winsor_pair good bin weight P total κ hκ hP htotal hsize hchunks hidx hinterval
  constructor
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos _ h.1
    intro a
    apply sub_nonneg.mpr
    exact Real.one_le_exp (mul_nonneg (by norm_num)
      (le_min (mul_nonneg hκ (Nat.cast_nonneg _)) (by norm_num)))
  · exact ofReal_sum_nat_bound _ κ _ scale hκ scale_pos (fun _ => le_max_left _ _) h.2

theorem capped_payoff_of_coverage_bound (x κ D : ℝ)
    (hx : 0 ≤ x) (hbound : x ≤ κ*D) :
    Real.exp (6*min x (6/5))-1 ≤ (maxFee : ℝ)*κ*D/scale ∧
    max 0 (x-6/5) ≤ κ*D := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  constructor
  · calc
      _ ≤ x*((maxFee : ℝ)/scale) := global_fee_sound x hx
      _ ≤ κ*D*((maxFee : ℝ)/scale) := mul_le_mul_of_nonneg_right hbound
        (div_nonneg (Nat.cast_nonneg _) hS.le)
      _ = _ := by ring
  · exact (max_le hx (by linarith)).trans hbound

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial ClaudeWCT.Numerics.N600
open ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedDigitBlock ClaudeWCT.Numerics.SharedPathList
open ClaudeWCT.Numerics.SharedPathCoordinate ClaudeWCT.Numerics.SharedPathPair
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
attribute [local irreducible] binnedPoly coordinatePoly coordinate SharedPathPacked.product SharedPathPacked.addFirst

noncomputable def actualGood {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Prop :=
  (∀ i, pairGood val (h.1 i)) ∧ coordinateGood val h.2
noncomputable def actualBin {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (h : ForestHistory β r) : Nat :=
  (∑ i, pairBin val (h.1 i))+coordinateBin val h.2
noncomputable def actualPoly (r : Nat) : Nat[X] :=
  encodedForestPoly (SharedPathPacked.pairFirst r) (coordinate 128 r).2

theorem coordinate_first_digit {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    digit (2^1024) (coordinate K r.val).2 j = (firstPoly K r.val).coeff j := by
  rw [coordinate_polynomial val hβ K hK r hp]
  exact ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) j _ (fun i => by
    have h1 := (coordinate_mass val hβ K hK r hp).2
    have h2 := polynomial_coeff_le_mass (firstPoly K r.val) i
    have h3 : 2^384<2^1024 := by decide +kernel
    exact h2.trans_lt (h1.trans h3))

theorem coordinate_first_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (K : Nat) (hK : K∈[64,128]) (r : Fin 21)
    (hp : ∀ j, (coordinatePoly K r.val).coeff j ≤
      (univ.filter fun E : Fin r.val → Fin K×β => coordinateCoverage val E=j).card) :
    ∀ j, digit (2^1024) (coordinate K r.val).2 j ≤
      (weightedHistogram (coordinateGood val) (coordinateBin val) (coordinateCoverage (C:=Fin K) (r:=r.val) val)).coeff j := by
  intro j
  rw [coordinate_first_digit val hβ K hK r hp]
  exact (coordinate_histogram val hβ K hK r hp).2 j

theorem actual_encoding {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    SharedPathPacked.forest r=(actualPoly r).eval (2^4096) := by
  exact encodedForest_encoding _ _ (pairFirst_histogram val hβ r hr (hp 64 (by simp))).1
    (coordinate_size val hβ 128 (by simp) ⟨r,by omega⟩ (hp 128 (by simp) r le_rfl)).2

theorem actual_histogram {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    CoeffLE (actualPoly r) (weightedHistogram (actualGood val) (actualBin val) (forestCoverage (r:=r) val)) := by
  classical
  exact encodedForest_histogram val r _ _ (pairGood val) (pairBin val)
    (coordinateGood val) (coordinateBin val)
    (pairFirst_histogram val hβ r hr (hp 64 (by simp))).2
    (fun j _ => coordinate_first_histogram val hβ 128 (by simp) ⟨r,by omega⟩
      (hp 128 (by simp) r le_rfl) j)

theorem actual_coeff_small {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) (j : Nat) :
    (actualPoly r).coeff j<2^4096 := by
  classical
  exact encodedForest_coeff_small val hβ r _ _ hr (pairGood val) (pairBin val)
    (coordinateGood val) (coordinateBin val)
    (pairFirst_histogram val hβ r hr (hp 64 (by simp))).2
    (fun j _ => coordinate_first_histogram val hβ 128 (by simp) ⟨r,by omega⟩
      (hp 128 (by simp) r le_rfl) j) j

theorem actual_interval {β : Type} [Fintype β] (val : β → Fin 6 → Nat)
    {r : Nat} (hr : 0<r) (h : ForestHistory β r) (hg : actualGood val h) :
    RoundedInterval 13 (actualBin val h) (forestCoverage val h : ℝ) := by
  exact forest_interval val r (pairGood val) (pairBin val) (coordinateGood val) (coordinateBin val)
    (fun h hh => pair_interval val hr h hh) (fun h hh => coordinate_interval val hr h hh) h hg

end ClaudeWCT.Numerics.SharedPathForest


namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial ClaudeWCT.Numerics.N600 ClaudeWCT.Numerics.SharedCoverage
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] fees scale maxFee

theorem rowDots_polynomial (r : Nat) (hr : r ≤ 20) (P : Nat[X])
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096) :
    rowDots r =
      ((∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).1)+
        maxFee*(forestMoment r-∑ j ∈ range 7210, P.coeff j),
       (∑ j ∈ range 7210, P.coeff j*(fees[j]?.getD (0,0)).2)+
        scale*(forestMoment r-∑ j ∈ range 7210, P.coeff j)) := by
  rw [rowDots, if_pos hr, henc, paidTree_polynomial_range 10 fees.toList P hc]
  simp only [Array.length_toList, fee_count, Array.getElem?_toList]

theorem rowDots_winsor_pair_ennreal {α : Type} [Fintype α]
    (good : α → Prop) [DecidablePred good] (bin weight : α → Nat)
    (r : Nat) (hr : r ≤ 20) (P : Nat[X]) (κ : ℝ) (hκ : 0 ≤ κ)
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096)
    (hP : CoeffLE P (weightedHistogram good bin weight))
    (htotal : (∑ a, weight a) = forestMoment r)
    (hsize : feeRuns.size = 1578)
    (hchunks : ∀ block : Nat, block < 25 → feeChunk block = true)
    (hinterval : ∀ a, good a →
      lowerValue (bin a) ≤ κ*(weight a : ℝ) ∧ κ*(weight a : ℝ) ≤ upperValue (bin a)) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((rowDots r).1 : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((rowDots r).2 : ENNReal) := by
  rw [rowDots_polynomial r hr P henc hc]
  exact histogram_winsor_pair_ennreal good bin weight P (forestMoment r) κ hκ
    hP htotal hsize hchunks fee_indices hinterval

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset
open scoped BigOperators ENNReal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] scale maxFee

theorem finite_payoff_global {α : Type} [Fintype α]
    (weight : α → Nat) (total : Nat) (κ : ℝ) (hκ : 0 ≤ κ)
    (htotal : (∑ a, weight a) = total) :
    (∑ a, ENNReal.ofReal (Real.exp (6*min (κ*(weight a : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((maxFee*total : Nat) : ENNReal) ∧
    (∑ a, ENNReal.ofReal (max 0 (κ*(weight a : ℝ)-6/5))) ≤
      ENNReal.ofReal κ/(scale : ENNReal)*((scale*total : Nat) : ENNReal) := by
  have hS : (0 : ℝ) < scale := by exact_mod_cast scale_pos
  have htotalR : (∑ a, (weight a : ℝ)) = (total : ℝ) := by exact_mod_cast htotal
  have hx (a : α) : 0 ≤ κ*(weight a : ℝ) := mul_nonneg hκ (Nat.cast_nonneg _)
  constructor
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos
      (fun a => sub_nonneg.mpr (Real.one_le_exp
        (mul_nonneg (by norm_num) (le_min (hx a) (by norm_num)))))
    calc
      _ ≤ ∑ a, κ*(weight a : ℝ)*((maxFee : ℝ)/scale) :=
        Finset.sum_le_sum (fun a _ => global_fee_sound _ (hx a))
      _ = κ/(scale : ℝ)*((maxFee*total : Nat) : ℝ) := by
        rw [← Finset.sum_mul, ← Finset.mul_sum, htotalR, Nat.cast_mul]
        ring
  · apply ofReal_sum_nat_bound _ κ _ scale hκ scale_pos (fun _ => le_max_left _ _)
    calc
      _ ≤ ∑ a, κ*(weight a : ℝ) := Finset.sum_le_sum
        (fun a _ => max_le (hx a) (by linarith))
      _ = κ/(scale : ℝ)*((scale*total : Nat) : ℝ) := by
        rw [← Finset.mul_sum, htotalR, Nat.cast_mul]
        field_simp

end ClaudeWCT.Numerics.SharedFees


namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.N600
open Finset Polynomial ClaudeWCT.Numerics.SharedCoverage ClaudeWCT.Numerics.SharedMoments
open ClaudeWCT.Numerics.SharedPathForest ClaudeWCT.Numerics.SharedPathList
open scoped BigOperators Polynomial ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem actual_forest_fee_row {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr0 : 0<r) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card)
    (htotal : (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r) :
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (Real.exp (6*min ((734:ℝ)/2^66*(forestCoverage val h : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((rowDots r).1:ENNReal) ∧
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (max 0 ((734:ℝ)/2^66*(forestCoverage val h : ℝ)-6/5))) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((rowDots r).2:ENNReal) := by
  classical
  exact rowDots_winsor_pair_ennreal (actualGood val) (actualBin val) (forestCoverage val)
    r hr (actualPoly r) ((734:ℝ)/2^66) (by positivity)
    (actual_encoding val hβ r hr hp) (actual_coeff_small val hβ r hr hp)
    (actual_histogram val hβ r hr hp) htotal fee_runs_count all_chunks
    (fun h hh => SharedPathList.RoundedInterval.fee_bounds (actual_interval val hr0 h hh))

theorem actual_forest_fee_global {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (r : Nat)
    (htotal : (∑ h : ForestHistory β r, forestCoverage val h) = forestMoment r) :
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (Real.exp (6*min ((734:ℝ)/2^66*(forestCoverage val h : ℝ)) (6/5))-1)) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((maxFee*forestMoment r:Nat):ENNReal) ∧
    (∑ h : ForestHistory β r, ENNReal.ofReal
      (max 0 ((734:ℝ)/2^66*(forestCoverage val h : ℝ)-6/5))) ≤
      ENNReal.ofReal ((734:ℝ)/2^66)/(scale:ENNReal)*((scale*forestMoment r:Nat):ENNReal) := by
  exact finite_payoff_global (forestCoverage val) (forestMoment r) ((734:ℝ)/2^66) (by positivity) htotal

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
open ClaudeWCT.Numerics.Kernel (fact)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

def pairChunkWith (coord : Nat → Nat → Cell) (r start size : Nat) : Nat :=
  let branches := (List.range (r+1)).map fun t => product (coord 64 t)
  (List.range' start size).foldl (fun acc t =>
    let a := branches.getD t (0,0)
    let b := branches.getD (r-t) (0,0)
    let row := if t=0 then b.2 else if r-t=0 then a.2 else addFirst a b
    acc + fact r / (fact t * fact (r-t)) * row) 0

theorem pairChunkWith_append (coord : Nat → Nat → Cell) (r start a b : Nat) :
    pairChunkWith coord r start (a+b) =
      pairChunkWith coord r start a + pairChunkWith coord r (start+a) b := by
  unfold pairChunkWith
  rw [← List.range'_append_1]
  simp only [foldl_weighted_sum, List.map_append, List.sum_append, Nat.zero_add]

theorem pairFirst_eq_chunk (r : Nat) :
    pairFirst r = pairChunkWith coordinate r 0 (r+1) := by
  unfold pairFirst pairChunkWith
  rw [List.range_eq_range']

theorem pairFirst_eq_two_chunks (r m : Nat) (hm : m ≤ r+1) :
    pairFirst r = pairChunkWith coordinate r 0 m +
      pairChunkWith coordinate r m (r+1-m) := by
  rw [pairFirst_eq_chunk, ← Nat.add_sub_of_le hm, pairChunkWith_append]
  simp only [Nat.zero_add, Nat.add_sub_cancel_left]

theorem pairChunkWith_congr (coord other : Nat → Nat → Cell) (r start size : Nat)
    (h : ∀ t, t ≤ r → coord 64 t = other 64 t) :
    pairChunkWith coord r start size = pairChunkWith other r start size := by
  have he : (List.range (r+1)).map (fun t => product (coord 64 t)) =
      (List.range (r+1)).map (fun t => product (other 64 t)) := by
    apply List.map_congr_left
    intro t ht
    rw [h t (by have := List.mem_range.mp ht; omega)]
  unfold pairChunkWith
  rw [he]

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedCoverage (foldl_weighted_sum)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairChunkWith_eq_singletons (coord : Nat → Nat → Cell) (r start size : Nat) :
    pairChunkWith coord r start size =
      ((List.range' start size).map (fun t => pairChunkWith coord r t 1)).sum := by
  unfold pairChunkWith
  simp only [foldl_weighted_sum, Nat.zero_add, List.range'_succ, List.range'_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

theorem pairFirst_eq_singletons (coord : Nat → Nat → Cell) (r : Nat)
    (h : ∀ t, t ≤ r → coordinate 64 t = coord 64 t) :
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum := by
  rw [pairFirst_eq_chunk, pairChunkWith_congr coordinate coord r 0 (r+1) h,
    pairChunkWith_eq_singletons, ← List.range_eq_range']

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def packTree (bits : Nat) : Nat → Nat → (Nat → Nat) → Nat
  | 0, start, f => f start
  | h+1, start, f =>
    packTree bits h start f + (packTree bits h (start+2^h) f <<< (bits*2^h))

theorem packTree_sum (bits h start : Nat) (f : Nat → Nat) :
    packTree bits h start f =
      ∑ i ∈ range (2^h), f (start+i)*(2^bits)^i := by
  induction h generalizing start with
  | zero => simp [packTree]
  | succ h ih =>
    rw [packTree, ih, ih, Nat.shiftLeft_eq, pow_mul]
    rw [show 2^(h+1)=2^h+2^h by omega]
    rw [Finset.sum_range_add]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    rw [Nat.add_assoc]
    ring

theorem packTree_reversed (bits h n : Nat) (f : Nat → Nat) (hn : n≤2^h) :
    packTree bits h 0 (fun i => if i<n then f (n-1-i) else 0) =
      (reverseFeePoly n f).eval (2^bits) := by
  rw [packTree_sum]
  simp only [Nat.zero_add, ite_mul, zero_mul]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  have hz : (∑ i ∈ Ico n (2^h), if i<n then f (n-1-i)*(2^bits)^i else 0)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [hz, Nat.add_zero]
  have hs : (∑ i ∈ range n, if i<n then f (n-1-i)*(2^bits)^i else 0)=
      ∑ i ∈ range n, f (n-1-i)*(2^bits)^i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  rw [hs, ← Finset.sum_range_reflect]
  simp only [reverseFeePoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro i hi
  have hi := Finset.mem_range.mp hi
  congr 2
  omega

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedPathForest
open Finset Polynomial SharedCoverage SharedMoments Thinning N600 SharedPathList
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem actual_mass_le {β : Type} [Fintype β]
    (val : β → Fin 6 → Nat) (hβ : Fintype.card β=563)
    (r : Nat) (hr : r≤20)
    (hp : ∀ K, K∈[64,128] → ∀ u, u≤r → ∀ j, (coordinatePoly K u).coeff j ≤
      (univ.filter fun E : Fin u → Fin K×β => coordinateCoverage val E=j).card) :
    (actualPoly r).eval 1≤alphabetSize^r*alphabetSize := by
  classical
  have hm := histogram_lower_mass_le (actualGood val) (actualBin val)
    (forestCoverage (r:=r) val) (actualPoly r) (actual_histogram val hβ r hr hp)
    alphabetSize (fun h _ => forest_coverage_le val hβ h)
  rwa [forest_history_card hβ r] at hm

end ClaudeWCT.Numerics.SharedPathForest

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false
attribute [local irreducible] fees maxFee scale

def feeValue (which i : Nat) : Nat :=
  if which=0 then 1 else if which=1 then (fees[i]?.getD (0,0)).1 else (fees[i]?.getD (0,0)).2

def packedFee (which : Nat) : Nat :=
  packTree 4096 13 0 (fun i => if i < 7210 then feeValue which (7209-i) else 0)

def packedDot (p q : Nat) : Nat := ((p*q) >>> (4096*7209)) % 2^4096

def convolutionDots (r p : Nat) : Nat × Nat :=
  let mass := packedDot p (packedFee 0)
  let lost := forestMoment r-mass
  (packedDot p (packedFee 1)+maxFee*lost, packedDot p (packedFee 2)+scale*lost)

theorem packedFee_model (which : Nat) :
    packedFee which = (reverseFeePoly 7210 (feeValue which)).eval (2^4096) := by
  exact packTree_reversed 4096 13 7210 (feeValue which) (by decide)

theorem convolution_shift (P : Nat[X]) (bits n : Nat) (f : Nat → Nat)
    (hmass : P.eval 1*(∑ i ∈ range n, f i) < 2^bits) :
    ((P.eval (2^bits)*(reverseFeePoly n f).eval (2^bits)) >>> (bits*(n-1))) % 2^bits =
      ∑ i ∈ range n, P.coeff i*f i := by
  rw [Nat.shiftRight_eq_div_pow, pow_mul]
  exact packed_convolution_dot P (2^bits) n f (by positivity) hmass

theorem packedDot_fee (P : Nat[X]) (p which : Nat)
    (hp : p=P.eval (2^4096))
    (hmass : P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096) :
    packedDot p (packedFee which) = ∑ i ∈ range 7210, P.coeff i*feeValue which i := by
  unfold packedDot
  rw [packedFee_model, hp]
  exact convolution_shift P 4096 7210 (feeValue which) hmass

theorem convolutionDots_model (P : Nat[X]) (r p : Nat)
    (hp : p=P.eval (2^4096))
    (hmass : ∀ which, which ≤ 2 → P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096) :
    convolutionDots r p =
      ((∑ i ∈ range 7210, P.coeff i*(fees[i]?.getD (0,0)).1)+
        maxFee*(forestMoment r-∑ i ∈ range 7210, P.coeff i),
       (∑ i ∈ range 7210, P.coeff i*(fees[i]?.getD (0,0)).2)+
        scale*(forestMoment r-∑ i ∈ range 7210, P.coeff i)) := by
  rw [convolutionDots, packedDot_fee P p 0 hp (hmass 0 (by decide)),
    packedDot_fee P p 1 hp (hmass 1 (by decide)),
    packedDot_fee P p 2 hp (hmass 2 (by decide))]
  simp only [feeValue, show ¬(1:Nat)=0 by decide, show ¬(2:Nat)=0 by decide,
    show ¬(2:Nat)=1 by decide, if_true, if_false, mul_one]

theorem feeValue_sum_small
    (hfee : ∀ i, i < 7210 → (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale)
    (hmax : maxFee ≤ 2^140) (hscale : scale ≤ 2^140) (which : Nat) :
    (∑ i ∈ range 7210, feeValue which i) < 2^160 := by
  have hb (i : Nat) (hi : i∈range 7210) : feeValue which i ≤ 2^140 := by
    unfold feeValue
    split_ifs
    · exact Nat.one_le_pow _ _ (by decide)
    · exact (hfee i (Finset.mem_range.mp hi)).1.trans hmax
    · exact (hfee i (Finset.mem_range.mp hi)).2.trans hscale
  calc
    _  ≤  ∑ _i ∈ range 7210, (2:Nat)^140 := Finset.sum_le_sum hb
    _ = 7210*2^140 := by simp
    _  <  2^160 := by decide +kernel

theorem convolution_mass_small (P : Nat[X])
    (hmass : P.eval 1 ≤ 2^3072)
    (hfee : ∀ i, i < 7210 → (fees[i]?.getD (0,0)).1 ≤ maxFee ∧ (fees[i]?.getD (0,0)).2 ≤ scale)
    (hmax : maxFee ≤ 2^140) (hscale : scale ≤ 2^140) (which : Nat) :
    P.eval 1*(∑ i ∈ range 7210, feeValue which i) < 2^4096 := by
  have hf := feeValue_sum_small hfee hmax hscale which
  exact (Nat.mul_le_mul hmass hf.le).trans_lt (by decide +kernel)

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
open Finset Polynomial
open ClaudeWCT.Numerics.SharedMoments
open scoped BigOperators Polynomial
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem maxFee_small : maxFee ≤ 2^140 := by decide +kernel
theorem scale_small : scale ≤ 2^140 := by decide +kernel

theorem forest_mass_3072 (r : Nat) (hr : r ≤ 20) :
    alphabetSize^r*alphabetSize ≤ 2^3072 := by
  have hp := Nat.pow_le_pow_right (n:=alphabetSize) (by decide : 0 < alphabetSize) hr
  exact (Nat.mul_le_mul_right _ hp).trans (by decide +kernel)

theorem rowDots_convolution (r : Nat) (hr : r ≤ 20) (P : Nat[X])
    (henc : SharedPathPacked.forest r = P.eval (2^4096))
    (hc : ∀ j, P.coeff j < 2^4096)
    (hmass : P.eval 1 ≤ 2^3072) :
    rowDots r = convolutionDots r (SharedPathPacked.forest r) := by
  have hfee := fees_bound_of_chunks fee_runs_count all_chunks fee_indices
  exact (rowDots_polynomial r hr P henc hc).trans
    (convolutionDots_model P r _ henc (fun w _ =>
      convolution_mass_small P hmass hfee maxFee_small scale_small w)).symm

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem packTree_congr (bits h a b : Nat) (f g : Nat → Nat)
    (hfg : ∀ i, i < 2^h → f (a+i)=g (b+i)) :
    packTree bits h a f=packTree bits h b g := by
  induction h generalizing a b with
  | zero => simpa [packTree] using hfg 0 (by decide)
  | succ h ih =>
    have hp : 2^(h+1)=2^h+2^h := by omega
    simp only [packTree]
    apply congrArg₂ Nat.add
    · apply ih
      intro i hi
      exact hfg i (by rw [hp]; omega)
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply ih
      intro i hi
      simpa only [Nat.add_assoc] using hfg (2^h+i) (by rw [hp]; omega)

def packList (bits : Nat) : Nat → List Nat → Nat
  | 0, xs => xs.headD 0
  | h+1, xs =>
    packList bits h (xs.take (2^h)) + (packList bits h (xs.drop (2^h)) <<< (bits*2^h))

theorem packList_eq_tree (bits h : Nat) (xs : List Nat) :
    packList bits h xs=packTree bits h 0 (fun i => xs[i]?.getD 0) := by
  induction h generalizing xs with
  | zero => cases xs <;> rfl
  | succ h ih =>
    rw [packList, ih, ih]
    conv_rhs => rw [packTree]
    apply congrArg₂ Nat.add
    · apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_take_of_lt hi]
    · apply congrArg (fun n => n <<< (bits*2^h))
      apply packTree_congr
      intro i hi
      simp only [Nat.zero_add, List.getElem?_drop]

end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

def feeVector (which : Nat) : List Nat :=
  feeEntries.map (fun e => if which=0 then 1 else if which=1 then e.2.1 else e.2.2)

def packedFeeVector (which : Nat) : Nat :=
  packList 4096 13 (feeVector which).reverse

theorem feeVector_length (which : Nat) (hl : feeEntries.length=7210) :
    (feeVector which).length=7210 := by simpa [feeVector] using hl

theorem feeVector_get (which i : Nat) (hl : feeEntries.length=7210) (hi : i < 7210) :
    (feeVector which)[i]?.getD 0=feeValue which i := by
  have h : i < feeEntries.length := by omega
  simp only [feeVector, feeValue, fees, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem h, Option.map_some, Option.getD_some]

theorem packedFeeVector_eq (which : Nat) (hl : feeEntries.length=7210) :
    packedFeeVector which=packedFee which := by
  rw [packedFeeVector, packList_eq_tree, packedFee]
  apply packTree_congr
  intro i hi
  simp only [Nat.zero_add]
  by_cases h : i < 7210
  · rw [List.getElem?_reverse (by rw [feeVector_length which hl]; exact h),
      feeVector_length which hl, if_pos h]
    exact feeVector_get which (7209-i) hl (by omega)
  · have hh : (feeVector which).reverse.length ≤ i := by
      rw [List.length_reverse, feeVector_length which hl]
      omega
    rw [List.getElem?_eq_none hh, if_neg h]
    rfl


end ClaudeWCT.Numerics.SharedFees

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open Lean Elab Command
open ClaudeWCT.Numerics.SharedFees
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

elab "fee_vector_numeral% " which:num : term =>
  return mkNatLit (packedFeeVector which.getNat)

elab "certify_fee_vector " which:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := fee_vector_numeral% $which))
  elabCommand (← `(theorem $proof : packedFeeVector $which = $cached := by decide +kernel))

certify_fee_vector 0 MassFee mass_fee_checked
certify_fee_vector 1 MgfFee mgf_fee_checked
certify_fee_vector 2 ResFee res_fee_checked
end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedGeneratedFeeVector
open ClaudeWCT.Numerics.SharedFees
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem feeEntries_length : feeEntries.length=7210 := by
  have h := congrArg List.length fee_indices
  simpa only [List.length_map, List.length_range] using h

theorem packedFee_0_checked : packedFee 0=MassFee :=
  (packedFeeVector_eq 0 feeEntries_length).symm.trans mass_fee_checked
theorem packedFee_1_checked : packedFee 1=MgfFee :=
  (packedFeeVector_eq 1 feeEntries_length).symm.trans mgf_fee_checked
theorem packedFee_2_checked : packedFee 2=ResFee :=
  (packedFeeVector_eq 2 feeEntries_length).symm.trans res_fee_checked

end ClaudeWCT.Numerics.SharedGeneratedFeeVector

namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem pairFirst_eq_cached_sum (coord : Nat → Nat → Cell) (chunks : Nat → Nat)
    (r : Nat)
    (hc : ∀ t, t ≤ r → ClaudeWCT.Numerics.SharedPathList.coordinate 64 t = coord 64 t)
    (hp : ∀ t, t ≤ r → pairChunkWith coord r t 1 = chunks t) :
    pairFirst r = ((List.range (r+1)).map chunks).sum := by
  calc
    pairFirst r = ((List.range (r+1)).map (fun t => pairChunkWith coord r t 1)).sum :=
      pairFirst_eq_singletons coord r hc
    _ = _ := congrArg List.sum (List.map_congr_left (fun t ht => hp t (by
      have := List.mem_range.mp ht
      omega)))

end ClaudeWCT.Numerics.SharedPathPacked

