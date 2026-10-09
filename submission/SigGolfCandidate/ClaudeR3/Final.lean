import SigGolfCandidate.ClaudeR3.Sums
import SigGolfCandidate.ClaudeR3.Checks
import SigGolfCandidate.ClaudeR3.Lemmas

section
namespace ClaudeR3.Ev
open Finset
open ClaudeR3.KEval
open ClaudeR3.Poly (tabSum)
open ClaudeR3.Tab (digit extCount levs Tab tabM tabN tabS)

theorem lsum_cons {α : Type} (f : α → ℕ) (a : α) (l : List α) : lsum f (a :: l) = f a + lsum f l := rfl

theorem nsum_eq (n : ℕ) (f : ℕ → ℕ) : nsum n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show f n + nsum n f = _
    rw [ih, sum_range_succ, add_comm]

theorem lsum_cast {α : Type} (f : α → ℕ) (l : List α) : (lsum f l : ℤ) = (l.map fun a => (f a : ℤ)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [lsum_cons, List.map_cons, List.sum_cons, ← ih]; push_cast; rfl

theorem dig_eq (k l : ℕ) : dig k l = digit k l := rfl

theorem extC_eq (e : ℕ) (he : e < 4) : extC e = extCount e := by
  have h := ClaudeR3.Tab.extCount_vals
  interval_cases e <;> simp [extC, h.1, h.2.1, h.2.2.1, h.2.2.2]

theorem extC_pos (e : ℕ) (he : e < 4) : 2 ≤ extC e := by
  interval_cases e <;> simp [extC]

theorem dsumN_cast (key : ℕ) : (dsumN key : ℤ) = dsumI key := by
  unfold dsumN dsumI
  rw [nsum_eq, rsum_eq]
  push_cast
  rfl

theorem rhoN_cast (key x : ℕ) : (rhoN key x : ℤ) = rhoI key (x : ℤ) := by
  unfold rhoN rhoI
  rw [nsum_eq, rsum_eq]
  push_cast
  rfl

theorem RtN_cast (x : ℕ) : (RtN x : ℤ) = RtI (x : ℤ) := by
  unfold RtN RtI
  rw [lsum_cast]
  push_cast
  rfl

theorem EtN_eq (x : ℕ) : EtN x = ∑ e ∈ range 4, extC e * x ^ e := by
  unfold EtN
  rw [nsum_eq]

theorem EtN_cast (x : ℕ) : (EtN x : ℤ) = EtI (x : ℤ) := by
  rw [EtN_eq]
  unfold EtI
  rw [rsum_eq]
  push_cast
  refine sum_congr rfl fun e he => ?_
  rw [extC_eq e (mem_range.mp he)]

theorem pow_le_EtN (e : ℕ) (he : e < 4) (x : ℕ) : 2 * x ^ e ≤ EtN x := by
  rw [EtN_eq]
  calc 2 * x ^ e ≤ extC e * x ^ e := Nat.mul_le_mul_right _ (extC_pos e he)
    _ ≤ ∑ e' ∈ range 4, extC e' * x ^ e' :=
        single_le_sum (f := fun e' => extC e' * x ^ e') (fun _ _ => Nat.zero_le _) (mem_range.mpr he)

theorem pow2_le_EtN (e f : ℕ) (he : e < 4) (hf : f < 4) (x : ℕ) : x ^ e + x ^ f ≤ EtN x := by
  by_cases hef : e = f
  · subst hef; have := pow_le_EtN e he x; omega
  · rw [EtN_eq]
    have hs : ({e, f} : Finset ℕ) ⊆ range 4 := by
      intro i hi; simp only [mem_insert, mem_singleton] at hi
      rcases hi with rfl | rfl <;> simpa using ‹_›
    calc x ^ e + x ^ f ≤ extC e * x ^ e + extC f * x ^ f :=
          Nat.add_le_add (Nat.le_mul_of_pos_left _ (by have := extC_pos e he; omega))
            (Nat.le_mul_of_pos_left _ (by have := extC_pos f hf; omega))
      _ = ∑ i ∈ ({e, f} : Finset ℕ), extC i * x ^ i := by rw [sum_pair hef]
      _ ≤ ∑ i ∈ range 4, extC i * x ^ i := sum_le_sum_of_subset hs

theorem AN_cast (e : ℕ) (he : e < 4) (x : ℕ) : (AN e x : ℤ) = AI e (x : ℤ) := by
  have h := pow_le_EtN e he x
  unfold AN AI
  rw [Nat.cast_mul, Nat.cast_sub (by omega), EtN_cast, RtN_cast]
  push_cast
  rfl

theorem AN2_cast (e f : ℕ) (he : e < 4) (hf : f < 4) (x : ℕ) :
    (AN2 e f x : ℤ) = ClaudeR3.Diff.AI2 e f (x : ℤ) := by
  have h := pow2_le_EtN e f he hf x
  unfold AN2 ClaudeR3.Diff.AI2
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_sub (by omega), EtN_cast, RtN_cast]
  push_cast
  rfl

theorem nPairN_cast (e f : ℕ) (he : e < 4) (hf : f < 4) : (nPairN e f : ℤ) = ClaudeR3.Diff.nPair e f := by
  have h1 := extC_pos e he
  have h2 := extC_pos f hf
  unfold nPairN ClaudeR3.Diff.nPair
  rw [← extC_eq e he, ← extC_eq f hf]
  split_ifs with h
  · rw [Nat.cast_sub (Nat.le_mul_of_pos_right _ (by omega))]
    push_cast; ring
  · rw [Nat.sub_zero]; push_cast; ring

theorem split_tab (tab : Tab) (F : ℕ → ℕ) :
    (tab.map fun a => (a.2 : ℤ) * (F a.1 : ℤ)).sum =
      (lsum (fun a => a.2 * F a.1) (posT tab) : ℤ) - (lsum (fun a => a.2 * F a.1) (negT tab) : ℤ) := by
  induction tab with
  | nil => rfl
  | cons a l ih =>
    obtain ⟨key, w⟩ := a
    cases w with
    | ofNat n =>
      show (((key, Int.ofNat n) :: l).map fun a => (a.2 : ℤ) * (F a.1 : ℤ)).sum =
        (lsum (fun a => a.2 * F a.1) ((key, n) :: posT l) : ℤ) - (lsum (fun a => a.2 * F a.1) (negT l) : ℤ)
      rw [List.map_cons, List.sum_cons, ih, lsum_cons]
      simp only [Int.ofNat_eq_coe]
      push_cast
      ring
    | negSucc n =>
      show (((key, Int.negSucc n) :: l).map fun a => (a.2 : ℤ) * (F a.1 : ℤ)).sum =
        (lsum (fun a => a.2 * F a.1) (posT l) : ℤ) - (lsum (fun a => a.2 * F a.1) ((key, n + 1) :: negT l) : ℤ)
      rw [List.map_cons, List.sum_cons, ih, lsum_cons, Int.negSucc_eq]
      push_cast
      ring

def castS (S : SN) : Sums ℤ := ⟨S.s0, S.s1x, S.s1y, S.s2⟩
def subS (P Q : Sums ℤ) : Sums ℤ := ⟨P.s0 - Q.s0, P.s1x - Q.s1x, P.s1y - Q.s1y, P.s2 - Q.s2⟩

theorem alpha_cast (base j : ℕ) (a : ℕ × ℤ) :
    (a.2 : ℤ) * ((base : ℤ) + dsumI a.1) ^ j = (a.2 : ℤ) * (((base + dsumN a.1) ^ j : ℕ) : ℤ) := by
  push_cast
  rw [dsumN_cast]

theorem sumsB_split (tab : Tab) (base j x y : ℕ) :
    ClaudeR3.Diff.sumsB (R := ℤ) tab base j (x : ℤ) (y : ℤ) =
      subS (castS (sumsN (posT tab) base j x y)) (castS (sumsN (negT tab) base j x y)) := by
  unfold ClaudeR3.Diff.sumsB subS castS sumsN
  simp only [Sums.mk.injEq, Int.cast_id]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.map_congr_left fun a _ => alpha_cast base j a]
    exact split_tab tab (fun key => (base + dsumN key) ^ j)
  · rw [List.map_congr_left fun a _ => show (a.2 : ℤ) * ((base : ℤ) + dsumI a.1) ^ j * rhoI a.1 (x : ℤ) =
        (a.2 : ℤ) * ((((base + dsumN a.1) ^ j * rhoN a.1 x : ℕ)) : ℤ) by
      push_cast; rw [dsumN_cast, rhoN_cast]; ring]
    rw [split_tab tab (fun key => (base + dsumN key) ^ j * rhoN key x)]
    simp only [aB, mul_assoc]
  · rw [rsum_eq, nsum_eq, nsum_eq]
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sub]
    congr 1
    rw [List.map_congr_left fun a _ => show (a.2 : ℤ) * ((base : ℤ) + dsumI a.1) ^ j * (digit a.1 l : ℤ) =
        (a.2 : ℤ) * ((((base + dsumN a.1) ^ j * dig a.1 l : ℕ)) : ℤ) by
      push_cast; rw [dsumN_cast]; simp only [dig_eq]; ring]
    rw [split_tab tab (fun key => (base + dsumN key) ^ j * dig key l)]
    simp only [aB, mul_assoc]
  · rw [rsum_eq, nsum_eq, nsum_eq]
    push_cast
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← mul_sub]
    congr 1
    rw [List.map_congr_left fun a _ => show
        (a.2 : ℤ) * ((base : ℤ) + dsumI a.1) ^ j * (digit a.1 l : ℤ) * rhoI a.1 (x : ℤ) =
        (a.2 : ℤ) * ((((base + dsumN a.1) ^ j * dig a.1 l * rhoN a.1 x : ℕ)) : ℤ) by
      push_cast; rw [dsumN_cast, rhoN_cast]; simp only [dig_eq]; ring]
    rw [split_tab tab (fun key => (base + dsumN key) ^ j * dig key l * rhoN key x)]
    simp only [aB, mul_assoc]

theorem sums_eq_sumsB {R : Type*} [CommRing R] (tab : Tab) (k : ℕ) (x y : R) :
    sums tab k x y = ClaudeR3.Diff.sumsB tab 71501 k x y := by
  unfold sums ClaudeR3.Diff.sumsB alphaI
  simp only [Nat.cast_ofNat]

theorem combine_sub (P Q : Sums ℤ) (x y : ℤ) : combine (subS P Q) x y = combine P x y - combine Q x y := by
  unfold combine subS
  rw [rsum_eq, rsum_eq, rsum_eq, ← sum_sub_distrib]
  refine sum_congr rfl fun e _ => ?_
  ring

theorem combine_cast (S : SN) (x y : ℕ) : combine (castS S) (x : ℤ) (y : ℤ) = (combineN S x y : ℤ) := by
  unfold combine combineN castS
  rw [rsum_eq, nsum_eq]
  push_cast
  refine sum_congr rfl fun e he => ?_
  have he4 := mem_range.mp he
  rw [← AN_cast e he4, ← AN_cast e he4, extC_eq e he4]

theorem famEval_split (tab : Tab) (k L x : ℕ) :
    famEval (R := ℤ) tab k L (x : ℤ) = (famP tab k L x : ℤ) - (famN tab k L x : ℤ) := by
  unfold famEval famP famN
  rw [show ((x : ℤ) ^ L) = ((x ^ L : ℕ) : ℤ) by push_cast; rfl, sums_eq_sumsB, sumsB_split, combine_sub,
    combine_cast, combine_cast]

theorem Wv_eq (tab : Tab) (k B : ℕ) : ClaudeR3.Asm.Wv tab k B = WvF tab k B := by
  unfold ClaudeR3.Asm.Wv WvF
  rw [famEval_split]
  omega

theorem nine_sub (e f : ℕ) (x y : ℤ) (P₁ P₂ Q₁ Q₂ : Sums ℤ) :
    ClaudeR3.Diff.nine e f x y (subS P₁ P₂) (subS Q₁ Q₂) =
      ClaudeR3.Diff.nine e f x y P₁ Q₁ + ClaudeR3.Diff.nine e f x y P₂ Q₂ -
        (ClaudeR3.Diff.nine e f x y P₁ Q₂ + ClaudeR3.Diff.nine e f x y P₂ Q₁) := by
  unfold ClaudeR3.Diff.nine subS
  ring

theorem nine_cast (e f : ℕ) (he : e < 4) (hf : f < 4) (x y : ℕ) (P Q : SN) :
    ClaudeR3.Diff.nine e f (x : ℤ) (y : ℤ) (castS P) (castS Q) = (nineN e f x y P Q : ℤ) := by
  unfold ClaudeR3.Diff.nine nineN castS
  rw [← AN2_cast e f he hf x, ← AN2_cast e f he hf y]
  push_cast
  ring

theorem dTerm_eq (t₁ t₂ : List (ℕ × ℕ)) (k L x j : ℕ) :
    (dTerm t₁ t₂ k L x j : ℤ) = ∑ e ∈ range 4, ∑ f ∈ range 4, (ClaudeR3.Diff.nPair e f : ℤ) *
      ClaudeR3.Diff.nine e f (x : ℤ) ((x ^ L : ℕ) : ℤ) (castS (sumsN t₁ 70938 j x (x ^ L)))
        (castS (sumsN t₂ 0 (k - j) x (x ^ L))) := by
  unfold dTerm
  rw [nsum_eq, Nat.cast_sum]
  refine sum_congr rfl fun e he => ?_
  rw [nsum_eq, Nat.cast_sum]
  refine sum_congr rfl fun f hf => ?_
  rw [Nat.cast_mul, nine_cast e f (mem_range.mp he) (mem_range.mp hf),
    nPairN_cast e f (mem_range.mp he) (mem_range.mp hf)]

theorem famEvalD_split (tab : Tab) (k L x : ℕ) :
    ClaudeR3.Diff.famEvalD (R := ℤ) tab k L (x : ℤ) = (famDP tab k L x : ℤ) - (famDN tab k L x : ℤ) := by
  unfold ClaudeR3.Diff.famEvalD famDP famDN
  rw [show ((x : ℤ) ^ L) = ((x ^ L : ℕ) : ℤ) by push_cast; rfl]
  simp only [sumsB_split]
  rw [rsum_eq, nsum_eq, nsum_eq, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_add, dTerm_eq, dTerm_eq, dTerm_eq, dTerm_eq]
  simp only [rsum_eq, Int.cast_id, nine_sub, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]

theorem Wv2_eq (k B : ℕ) : ClaudeR3.Asm.Wv2 k B = Wv2F k B := by
  unfold ClaudeR3.Asm.Wv2 Wv2F
  rw [famEval_split, famEvalD_split]
  omega

theorem lsum_mul_left {α : Type} (c : ℕ) (f : α → ℕ) (l : List α) : lsum (fun a => c * f a) l = c * lsum f l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [lsum_cons, lsum_cons, ih, mul_add]

theorem lsum_sum {α : Type} (s : Finset ℕ) (g : α → ℕ → ℕ) (l : List α) :
    lsum (fun a => ∑ i ∈ s, g a i) l = ∑ i ∈ s, lsum (fun a => g a i) l := by
  induction l with
  | nil => exact (sum_const_zero).symm
  | cons a l ih =>
    rw [lsum_cons, ih]
    simp only [lsum_cons]
    rw [sum_add_distrib]

theorem lsum_congr' {α : Type} {f g : α → ℕ} (h : ∀ a, f a = g a) (l : List α) : lsum f l = lsum g l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [lsum_cons, lsum_cons, h a, ih]

theorem nsum_congr {n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) : nsum n f = nsum n g := by
  rw [nsum_eq, nsum_eq]
  exact sum_congr rfl fun i hi => h i (mem_range.mp hi)

theorem rhoN_eq (key x : ℕ) : rhoN key x = ∑ m ∈ range 15, x ^ m * dig key m := by
  unfold rhoN
  rw [nsum_eq]
  exact sum_congr rfl fun m _ => mul_comm _ _

theorem lsum_rho (t : List (ℕ × ℕ)) (F : ℕ × ℕ → ℕ) (x : ℕ) :
    lsum (fun a => F a * rhoN a.1 x) t = ∑ m ∈ range 15, x ^ m * lsum (fun a => F a * dig a.1 m) t := by
  rw [lsum_congr' (fun a => show F a * rhoN a.1 x = ∑ m ∈ range 15, x ^ m * (F a * dig a.1 m) by
    rw [rhoN_eq, mul_sum]; exact sum_congr rfl fun m _ => by ring) t, lsum_sum]
  exact sum_congr rfl fun m _ => lsum_mul_left _ _ _

theorem tq2_comm (t : List (ℕ × ℕ)) (base j l m : ℕ) : tq2 t base j l m = tq2 t base j m l := by
  unfold tq2
  exact lsum_congr' (fun a => by ring) t

theorem sumsN_eq_L (t : List (ℕ × ℕ)) (base j : ℕ) (lit : List ℕ) (h : tqOk t base j lit = true) (x y : ℕ) :
    sumsN t base j x y = sumsL lit x y := by
  unfold tqOk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨h0, h1⟩, h2⟩ := h
  have hm2 : ∀ l < 15, ∀ m < 15, lit.getD (sidx (min l m) (max l m)) 0 = tq2 t base j l m := by
    intro l hl m hm
    have := h2 (min l m) (by omega) (max l m - min l m) (by omega)
    rw [show min l m + (max l m - min l m) = max l m by omega] at this
    rw [← this]
    rcases le_total l m with hlm | hlm
    · rw [min_eq_left hlm, max_eq_right hlm]
    · rw [min_eq_right hlm, max_eq_left hlm, tq2_comm]
  unfold sumsN sumsL
  rw [SN.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h0]; rfl
  · rw [lsum_rho, nsum_eq]
    exact sum_congr rfl fun m hm => by
      rw [← h1 m (mem_range.mp hm)]; rfl
  · refine nsum_congr fun l hl => ?_
    rw [← h1 l hl]; rfl
  · refine nsum_congr fun l hl => ?_
    rw [lsum_rho, nsum_eq]
    refine congrArg (y ^ l * ·) (sum_congr rfl fun m hm => ?_)
    rw [hm2 l hl m (mem_range.mp hm)]
    rfl

theorem famDP_eq_L0 (k L x : ℕ) (hk : k ≤ 18) : famDP tabM k L x = famDPL0 k L x := by
  unfold famDP famDPL0
  refine nsum_congr fun j hj => ?_
  unfold dTerm dTermL
  rw [sumsN_eq_L _ _ _ _ (tqPA_all j (by omega)),
    sumsN_eq_L _ _ _ _ (tqPB_all (k - j) (by omega)),
    sumsN_eq_L _ _ _ _ (tqNA_all j (by omega)),
    sumsN_eq_L _ _ _ _ (tqNB_all (k - j) (by omega))]

theorem famDN_eq_L0 (k L x : ℕ) (hk : k ≤ 18) : famDN tabM k L x = famDNL0 k L x := by
  unfold famDN famDNL0
  refine nsum_congr fun j hj => ?_
  unfold dTerm dTermL
  rw [sumsN_eq_L _ _ _ _ (tqPA_all j (by omega)),
    sumsN_eq_L _ _ _ _ (tqNB_all (k - j) (by omega)),
    sumsN_eq_L _ _ _ _ (tqNA_all j (by omega)),
    sumsN_eq_L _ _ _ _ (tqPB_all (k - j) (by omega))]

theorem nineN_eq (e f x y : ℕ) (P Q : SN) : nineN e f x y P Q = nine9 e f x y (pairsN P Q) := by
  unfold nineN nine9 pairsN
  ring

theorem nine9_conv (P Q : List (List ℕ)) (k L x e f : ℕ) :
    nine9 e f x (x ^ L) (convN P Q k L x) = ∑ j ∈ range (k + 1), k.choose j *
      nine9 e f x (x ^ L) (pairsN (sumsL (P.getD j []) x (x ^ L)) (sumsL (Q.getD (k - j) []) x (x ^ L))) := by
  unfold convN nine9
  simp only [nsum_eq, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem sum_dTermL (P Q : List (List ℕ)) (k L x : ℕ) :
    nsum (k + 1) (fun j => k.choose j * dTermL P Q k L x j) = dSumL P Q k L x := by
  unfold dTermL dSumL
  simp only [nsum_eq, nine9_conv, nineN_eq, mul_sum]
  rw [sum_comm (s := range (k + 1))]
  refine sum_congr rfl fun e _ => ?_
  rw [sum_comm (s := range (k + 1))]
  refine sum_congr rfl fun f _ => ?_
  exact sum_congr rfl fun j _ => by ring

theorem famDPL0_eq (k L x : ℕ) : famDPL0 k L x = famDPL k L x := by
  unfold famDPL0 famDPL
  simp only [mul_add]
  rw [← sum_dTermL, ← sum_dTermL, nsum_eq, nsum_eq, nsum_eq, sum_add_distrib]

theorem famDNL0_eq (k L x : ℕ) : famDNL0 k L x = famDNL k L x := by
  unfold famDNL0 famDNL
  simp only [mul_add]
  rw [← sum_dTermL, ← sum_dTermL, nsum_eq, nsum_eq, nsum_eq, sum_add_distrib]

theorem famDP_eq_L (k L x : ℕ) (hk : k ≤ 18) : famDP tabM k L x = famDPL k L x := by
  rw [famDP_eq_L0 k L x hk, famDPL0_eq]

theorem famDN_eq_L (k L x : ℕ) (hk : k ≤ 18) : famDN tabM k L x = famDNL k L x := by
  rw [famDN_eq_L0 k L x hk, famDNL0_eq]

theorem Wv2F_eq_L (k B : ℕ) (hk : k ≤ 18) : Wv2F k B = Wv2L k B := by
  unfold Wv2F Wv2L
  rw [famDP_eq_L k 154 B hk, famDN_eq_L k 154 B hk]

theorem sumsN_one (t : List (ℕ × ℕ)) (base j : ℕ) : sumsN t base j 1 1 = sums1N t base j := by
  have hrho : ∀ key, rhoN key 1 = dsumN key := fun key => by
    unfold rhoN dsumN; simp only [one_pow, mul_one]
  have hds : ∀ key, dsumN key = ∑ l ∈ range 15, dig key l := fun key => by unfold dsumN; rw [nsum_eq]
  unfold sumsN sums1N
  rw [SN.mk.injEq]
  refine ⟨rfl, lsum_congr' (fun a => by rw [hrho]) t, ?_, ?_⟩
  · simp only [one_pow, one_mul]
    rw [nsum_eq, ← lsum_sum]
    refine lsum_congr' (fun a => ?_) t
    rw [hds a.1, mul_sum]
  · simp only [one_pow, one_mul, hrho]
    rw [nsum_eq, ← lsum_sum]
    refine lsum_congr' (fun a => ?_) t
    rw [show aB base j a * dsumN a.1 * dsumN a.1 = (∑ l ∈ range 15, aB base j a * dig a.1 l) * dsumN a.1 by
      rw [← mul_sum, ← hds], sum_mul]

theorem famP_one (tab : Tab) (k L : ℕ) : famP tab k L 1 = famP1 tab k := by
  unfold famP famP1
  rw [one_pow, sumsN_one]

theorem famN_one (tab : Tab) (k L : ℕ) : famN tab k L 1 = famN1 tab k := by
  unfold famN famN1
  rw [one_pow, sumsN_one]

theorem WvF_one (tab : Tab) (k : ℕ) : WvF tab k 1 = WvF1 tab k := by
  unfold WvF WvF1
  rw [famP_one, famN_one]

theorem Wv2L_one (k : ℕ) : Wv2L k 1 = Wv2L1 k := by
  unfold Wv2L Wv2L1
  rw [famP_one, famN_one]

theorem bonfN_eq : ClaudeR3.Asm.bonfN = bonfNF := rfl

end ClaudeR3.Ev

namespace ClaudeR3.BonfData
open ClaudeR3.Asm
open ClaudeR3.Ev

noncomputable def meanCheckR (r : Nat) : Bool :=
  meanOk (r - 2) 104 (2 ^ meanBB.getD r 0) &&
    Nat.ble (bonfMeanN (r - 2) 104 (meanRp.getD r 0) (2 ^ meanBB.getD r 0)) (meanD.getD r 0)
noncomputable def nearCheckR (r : Nat) : Bool :=
  nearOk (r - 2) 104 (2 ^ nearBB.getD r 0) &&
    Nat.ble (bonfNearN (r - 2) 104 (nearRp.getD r 0) (2 ^ nearBB.getD r 0)) (nearD.getD r 0)
noncomputable def diagCheckR (r : Nat) : Bool :=
  diagOk (r - 2) 104 (2 ^ diagBB.getD r 0) &&
    Nat.ble (bonfDiagN (r - 2) 104 (diagRp.getD r 0) (2 ^ diagBB.getD r 0)) (diagD.getD r 0)

theorem meanCheck_eq (r : ℕ) : meanCheckR r = meanCheckF r := by
  unfold meanCheckR meanCheckF meanOk bonfMeanN
  simp only [Wv_eq, bonfN_eq, WvF_one]

theorem nearCheck_eq (r : ℕ) : nearCheckR r = nearCheckF r := by
  unfold nearCheckR nearCheckF nearOk bonfNearN
  simp only [Wv_eq, bonfN_eq, WvF_one]

theorem diagCheck_eq (r : ℕ) (hr : r ≤ 20) : diagCheckR r = diagCheckL r := by
  unfold diagCheckR diagCheckL diagOk bonfDiagN
  simp only [Wv2_eq, bonfN_eq, Wv2F_eq_L (r - 2) _ (by omega), Wv2L_one]

end ClaudeR3.BonfData
end

section
namespace ClaudeR3.BonfData
open ClaudeR3.Ev

theorem mean_r2 : meanCheckR 2 = true := (meanCheck_eq 2).trans meanF_r2
theorem mean_r3 : meanCheckR 3 = true := (meanCheck_eq 3).trans meanF_r3
theorem mean_r4 : meanCheckR 4 = true := (meanCheck_eq 4).trans meanF_r4
theorem mean_r5 : meanCheckR 5 = true := (meanCheck_eq 5).trans meanF_r5
theorem mean_r6 : meanCheckR 6 = true := (meanCheck_eq 6).trans meanF_r6
theorem mean_r7 : meanCheckR 7 = true := (meanCheck_eq 7).trans meanF_r7
theorem mean_r8 : meanCheckR 8 = true := (meanCheck_eq 8).trans meanF_r8
theorem mean_r9 : meanCheckR 9 = true := (meanCheck_eq 9).trans meanF_r9
theorem mean_r10 : meanCheckR 10 = true := (meanCheck_eq 10).trans meanF_r10
theorem mean_r11 : meanCheckR 11 = true := (meanCheck_eq 11).trans meanF_r11
theorem mean_r12 : meanCheckR 12 = true := (meanCheck_eq 12).trans meanF_r12
theorem mean_r13 : meanCheckR 13 = true := (meanCheck_eq 13).trans meanF_r13
theorem mean_r14 : meanCheckR 14 = true := (meanCheck_eq 14).trans meanF_r14
theorem mean_r15 : meanCheckR 15 = true := (meanCheck_eq 15).trans meanF_r15
theorem mean_r16 : meanCheckR 16 = true := (meanCheck_eq 16).trans meanF_r16
theorem mean_r17 : meanCheckR 17 = true := (meanCheck_eq 17).trans meanF_r17
theorem mean_r18 : meanCheckR 18 = true := (meanCheck_eq 18).trans meanF_r18
theorem mean_r19 : meanCheckR 19 = true := (meanCheck_eq 19).trans meanF_r19
theorem mean_r20 : meanCheckR 20 = true := (meanCheck_eq 20).trans meanF_r20

end ClaudeR3.BonfData
end

section
namespace ClaudeR3.BonfData
open ClaudeR3.Ev

theorem near_r2 : nearCheckR 2 = true := (nearCheck_eq 2).trans nearF_r2
theorem near_r3 : nearCheckR 3 = true := (nearCheck_eq 3).trans nearF_r3
theorem near_r4 : nearCheckR 4 = true := (nearCheck_eq 4).trans nearF_r4
theorem near_r5 : nearCheckR 5 = true := (nearCheck_eq 5).trans nearF_r5
theorem near_r6 : nearCheckR 6 = true := (nearCheck_eq 6).trans nearF_r6
theorem near_r7 : nearCheckR 7 = true := (nearCheck_eq 7).trans nearF_r7
theorem near_r8 : nearCheckR 8 = true := (nearCheck_eq 8).trans nearF_r8
theorem near_r9 : nearCheckR 9 = true := (nearCheck_eq 9).trans nearF_r9
theorem near_r10 : nearCheckR 10 = true := (nearCheck_eq 10).trans nearF_r10
theorem near_r11 : nearCheckR 11 = true := (nearCheck_eq 11).trans nearF_r11
theorem near_r12 : nearCheckR 12 = true := (nearCheck_eq 12).trans nearF_r12
theorem near_r13 : nearCheckR 13 = true := (nearCheck_eq 13).trans nearF_r13
theorem near_r14 : nearCheckR 14 = true := (nearCheck_eq 14).trans nearF_r14
theorem near_r15 : nearCheckR 15 = true := (nearCheck_eq 15).trans nearF_r15
theorem near_r16 : nearCheckR 16 = true := (nearCheck_eq 16).trans nearF_r16
theorem near_r17 : nearCheckR 17 = true := (nearCheck_eq 17).trans nearF_r17
theorem near_r18 : nearCheckR 18 = true := (nearCheck_eq 18).trans nearF_r18
theorem near_r19 : nearCheckR 19 = true := (nearCheck_eq 19).trans nearF_r19
theorem near_r20 : nearCheckR 20 = true := (nearCheck_eq 20).trans nearF_r20

end ClaudeR3.BonfData
end

section
namespace ClaudeR3.BonfData
open ClaudeR3.Ev

theorem diag_r2 : diagCheckR 2 = true := (diagCheck_eq 2 (by norm_num)).trans diagF_r2
theorem diag_r3 : diagCheckR 3 = true := (diagCheck_eq 3 (by norm_num)).trans diagF_r3
theorem diag_r4 : diagCheckR 4 = true := (diagCheck_eq 4 (by norm_num)).trans diagF_r4
theorem diag_r5 : diagCheckR 5 = true := (diagCheck_eq 5 (by norm_num)).trans diagF_r5
theorem diag_r6 : diagCheckR 6 = true := (diagCheck_eq 6 (by norm_num)).trans diagF_r6
theorem diag_r7 : diagCheckR 7 = true := (diagCheck_eq 7 (by norm_num)).trans diagF_r7
theorem diag_r8 : diagCheckR 8 = true := (diagCheck_eq 8 (by norm_num)).trans diagF_r8
theorem diag_r9 : diagCheckR 9 = true := (diagCheck_eq 9 (by norm_num)).trans diagF_r9
theorem diag_r10 : diagCheckR 10 = true := (diagCheck_eq 10 (by norm_num)).trans diagF_r10
theorem diag_r11 : diagCheckR 11 = true := (diagCheck_eq 11 (by norm_num)).trans diagF_r11
theorem diag_r12 : diagCheckR 12 = true := (diagCheck_eq 12 (by norm_num)).trans diagF_r12
theorem diag_r13 : diagCheckR 13 = true := (diagCheck_eq 13 (by norm_num)).trans diagF_r13
theorem diag_r14 : diagCheckR 14 = true := (diagCheck_eq 14 (by norm_num)).trans diagF_r14
theorem diag_r15 : diagCheckR 15 = true := (diagCheck_eq 15 (by norm_num)).trans diagF_r15
theorem diag_r16 : diagCheckR 16 = true := (diagCheck_eq 16 (by norm_num)).trans diagF_r16
theorem diag_r17 : diagCheckR 17 = true := (diagCheck_eq 17 (by norm_num)).trans diagF_r17
theorem diag_r18 : diagCheckR 18 = true := (diagCheck_eq 18 (by norm_num)).trans diagF_r18
theorem diag_r19 : diagCheckR 19 = true := (diagCheck_eq 19 (by norm_num)).trans diagF_r19
theorem diag_r20 : diagCheckR 20 = true := (diagCheck_eq 20 (by norm_num)).trans diagF_r20

end ClaudeR3.BonfData
end

section
namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN priceScale priceScale_mul card_index env_moment xNum Nn Q A
  card_table w1_table)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum lawAvg_le_uniform law_marked_atIndex
  lawAvg_mono lawAvg_const)
open ClaudeWCT.Numerics.Thinning (env env_le_one ListCov)
open SphincsSecurity.Concrete (binomialAverage uniformWordAverage)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (capS J779 card_capS779 capS779_nonempty)
open ClaudeR3.BonfData

abbrev Coords := Fin 9 → Child × Rank

noncomputable def honest779 : Coords → ENNReal := uniformOn (capS 779)

theorem card_coords : Fintype.card Coords = Q ^ 9 := card_table (Fintype.card_fin 563) (Fintype.card_fin 128)

theorem uniformOn_sum_one {β : Type} [Fintype β] {C : Type} [Fintype C] [DecidableEq C]
    (S : Finset (Fin 9 → C × β)) (hS : S.Nonempty) : ∑ x, uniformOn S x = 1 := by
  classical
  unfold uniformOn
  rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel (by simp [hS.ne_empty])
    (ENNReal.natCast_ne_top _)]

theorem honest_sum_one : ∑ x, honest779 x = 1 := uniformOn_sum_one (capS 779) capS779_nonempty

noncomputable def kappa779 : ENNReal := ((Q ^ 9 : ℕ) : ENNReal) / (J779 : ENNReal)

theorem honest_density (x : Coords) : honest779 x ≤ kappa779 * (Fintype.card Coords : ENNReal)⁻¹ := by
  classical
  unfold honest779 uniformOn kappa779
  rw [card_coords, ← card_capS779]
  split_ifs
  · rw [div_eq_mul_inv, mul_comm, ← mul_assoc, ENNReal.inv_mul_cancel (by simp [Q]) (ENNReal.natCast_ne_top _),
      one_mul]
  · exact zero_le

theorem density_to_J (r X : ℕ) :
    kappa779 ^ r * ((X : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) =
      1 ^ r * (((128 ^ 9 * X : ℕ) : ENNReal) / ((Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  unfold kappa779
  have hJ : (0 : ℝ) < J779 := by unfold J779; norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)) ?_
      · unfold J779; simp
      · exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by simp [Nn, Q]))
    (by
      refine ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)
      unfold J779; simp [Q])).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, one_pow,
    one_mul]
  push_cast
  have hJ' : (J779 : ℝ) ≠ 0 := hJ.ne'
  have hN : (Nn : ℝ) ≠ 0 := by norm_num [Nn]
  rw [div_pow, ← pow_mul, show (Q : ℝ) = 128 * Nn by norm_num [Q, Nn]]
  field_simp
  ring

theorem mean_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : meanCheckR r = true := by
  interval_cases r
  exacts [mean_r2, mean_r3, mean_r4, mean_r5, mean_r6, mean_r7, mean_r8, mean_r9, mean_r10, mean_r11, mean_r12,
    mean_r13, mean_r14, mean_r15, mean_r16, mean_r17, mean_r18, mean_r19, mean_r20]

set_option maxRecDepth 10000 in
theorem meanRp_le : ∀ r, 2 ≤ r → r ≤ 20 → meanRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide

def fMean (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then meanD.getD r 0 else 128 ^ 9 * xNum r ^ 9

theorem mean_pay [SampleableType Coords] (r : ℕ) :
    lawAvg honest779 r (env (n := 9) (C := Child) wordDigit) ≤
      1 ^ r * ((fMean r : ENNReal) / ((Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := mean_check_all (k + 2) hr.1 hr.2
    unfold meanCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.mean_bound k 104 (meanRp.getD (k + 2) 0) (2 ^ meanBB.getD (k + 2) 0) (by norm_num)
      (meanRp_le (k + 2) (by omega) hr.2) hok
    have hcount := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (capS 779) (fun L t => ListCov wordDigit L t)
    show lawAvg (uniformOn (capS 779)) (k + 2) (fun L => SigGolfResearch.Gate6.Moments.finiteAverage
      (fun t => if ListCov wordDigit L t then 1 else 0)) ≤ _
    rw [hcount, card_capS779, card_coords, one_pow, one_mul, fMean, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    calc _ ≤ ((meanD.getD (k + 2) 0 : ℕ) : ENNReal) / ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal)) :=
          ENNReal.div_le_div_right (by exact_mod_cast hb.trans hle) _
      _ = _ := by push_cast; ring_nf
  · have hd := lawAvg_le_uniform honest779 kappa779 honest_density r (env (n := 9) (C := Child) wordDigit)
    rw [env_moment wordDigit (Fintype.card_fin 563) (Fintype.card_fin 128)
      (fun p => w1_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p) r,
      density_to_J] at hd
    rw [fMean, if_neg hr]
    exact hd

theorem mean_pay_one (r : ℕ) : lawAvg honest779 r (env (n := 9) (C := Child) wordDigit) ≤ 1 :=
  (lawAvg_mono honest779 r (env_le_one wordDigit)).trans_eq (lawAvg_const honest779 honest_sum_one r 1)

theorem price_mean_eq (T : ℕ) :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) =
      (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T
        (fun r => lawAvg honest779 r (env (n := 9) (C := Child) wordDigit)) := by
  unfold priceN
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [law_marked_atIndex honest779 honest_sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul]

def meanJCheck : Bool :=
  ClaudeR3.PoissonJ.poissonCheckJ J779 13533529 100000000 2 1 fMean (Q ^ 9) A 1 602 1000 80

end ClaudeR3.Final
end

section
namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN nearPriceN nearLoad priceScale priceScale_mul card_index env_moment
  env_sq_moment nearEnv_moment xNum xfNum xfSum xfSum_eq yNum Nn Q A Kc card_table w1_table w2_table wf_table)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum lawAvg_le_uniform law_marked_atIndex
  lawAvg_mono lawAvg_const)
open ClaudeWCT.Numerics.Thinning (env env_le_one env_sq ListCov ListCovExcept nearEnv nearEnv_le_one)
open SphincsSecurity.Concrete (binomialAverage uniformWordAverage)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (capS J779 card_capS779 capS779_nonempty)
open ClaudeR3.BonfData

theorem w1T : ClaudeWCT.Numerics.N600.W1Table wordDigit :=
  fun p => w1_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p
theorem w2T : ClaudeWCT.Numerics.N600.W2Table wordDigit :=
  fun p => w2_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) p
theorem wfT (i : Fin 6) : ClaudeWCT.Numerics.N600.WFTable wordDigit i :=
  fun p => wf_table ClaudeR3.Tab.wordsOf_wordDigit' (fun x j => ClaudeR3.Tab.wordDigit_le4 x j) i p

theorem near_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : nearCheckR r = true := by
  interval_cases r
  exacts [near_r2, near_r3, near_r4, near_r5, near_r6, near_r7, near_r8, near_r9, near_r10, near_r11, near_r12, near_r13, near_r14, near_r15, near_r16, near_r17, near_r18, near_r19, near_r20]

theorem diag_check_all (r : ℕ) (h1 : 2 ≤ r) (h2 : r ≤ 20) : diagCheckR r = true := by
  interval_cases r
  exacts [diag_r2, diag_r3, diag_r4, diag_r5, diag_r6, diag_r7, diag_r8, diag_r9, diag_r10, diag_r11, diag_r12, diag_r13, diag_r14, diag_r15, diag_r16, diag_r17, diag_r18, diag_r19, diag_r20]

def fNear (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then nearD.getD r 0 else 9 * 128 ^ 9 * (xNum r ^ 8 * xfSum r)
def fDiag (r : ℕ) : ℕ := if 2 ≤ r ∧ r ≤ 20 then diagD.getD r 0 else 128 ^ 9 * yNum r ^ 9

theorem rp_le (L : List ℕ) (k : ℕ) (h : ∀ r, 2 ≤ r → r ≤ 20 → L.getD r 0 ≤ r) (hk : k + 2 ≤ 20) :
    L.getD (k + 2) 0 ≤ k + 2 := h (k + 2) (by omega) hk

set_option maxRecDepth 10000 in
theorem nearRp_le : ∀ r, 2 ≤ r → r ≤ 20 → nearRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide
set_option maxRecDepth 10000 in
theorem diagRp_le : ∀ r, 2 ≤ r → r ≤ 20 → diagRp.getD r 0 ≤ r := by
  intro r h1 h2; interval_cases r <;> decide

theorem density_conv (r X n c : ℕ) (hn : 0 < n) (hc : 0 < c) :
    kappa779 ^ r * ((X : ENNReal) / ((n * Q ^ (9 * r) : ℕ) : ENNReal)) =
      1 ^ r * (((c * X : ℕ) : ENNReal) / ((c * n * J779 ^ r : ℕ) : ENNReal)) := by
  unfold kappa779
  have hJ : (0 : ℝ) < J779 := by unfold J779; norm_num
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have hQ : (0 : ℝ) < (Q : ℝ) := by unfold Q; norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by
      refine ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)) ?_
      · unfold J779; simp
      · refine ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_
        have : 0 < n * Q ^ (9 * r) := by unfold Q; positivity
        exact_mod_cast this.ne')
    (by
      refine ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) ?_)
      have : 0 < c * n * J779 ^ r := by unfold J779; positivity
      exact_mod_cast this.ne')).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, one_pow,
    one_mul]
  push_cast
  have hJ' : (J779 : ℝ) ≠ 0 := hJ.ne'
  rw [pow_mul, div_pow]
  field_simp
  try ring

section Pay
variable [SampleableType Coords]

theorem nearEnv_density (k : Fin 9) (t : Fin 6) (r : ℕ) :
    lawAvg honest779 r (nearEnv (C := Child) wordDigit k t) ≤
      kappa779 ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  rw [← nearEnv_moment wordDigit k t (Fintype.card_fin 563) (Fintype.card_fin 128) w1T (wfT t) r]
  exact lawAvg_le_uniform honest779 kappa779 honest_density r _

theorem nearLoad_density (r : ℕ) :
    nearLoad wordDigit (vc := honest779) (C := Child) r ≤
      kappa779 ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / ((6 * Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)) := by
  unfold nearLoad
  set D : ENNReal := ((Nn ^ 9 * Q ^ (9 * r) : ℕ) : ENNReal)
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg honest779 r (nearEnv (C := Child) wordDigit k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ t : Fin 6, kappa779 ^ r * (((xNum r ^ 8 * xfNum t r : ℕ) : ENNReal) / D) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ => nearEnv_density k t r)
    _ = kappa779 ^ r * (((xNum r ^ 8 * xfSum r : ℕ) : ENNReal) / (6 * D)) := by
        rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        have h63 : (54 : ENNReal)⁻¹ * ((9 : ℕ) : ENNReal) = 6⁻¹ := by
          rw [show (54 : ENNReal) = 9 * 6 by norm_num, ENNReal.mul_inv (by simp) (by simp), Nat.cast_ofNat,
            mul_comm (9 : ENNReal)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simp) (by simp), mul_one]
        rw [h63, xfSum_eq, show xNum r ^ 8 * ∑ t : Fin 6, xfNum t r = ∑ t : Fin 6, xNum r ^ 8 * xfNum t r from
          Finset.mul_sum _ _ _, Nat.cast_sum]
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine sum_congr rfl fun t _ => ?_
        ring
    _ = _ := by simp only [D]; push_cast; ring_nf

theorem near_pay (r : ℕ) :
    nearLoad wordDigit (vc := honest779) (C := Child) r ≤
      1 ^ r * ((fNear r : ENNReal) / ((54 * Q ^ 9 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := near_check_all (k + 2) hr.1 hr.2
    unfold nearCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.near_bound k 104 (nearRp.getD (k + 2) 0) (2 ^ nearBB.getD (k + 2) 0) (by norm_num)
      (rp_le nearRp k nearRp_le hr.2) hok
    have hcount : ∀ (k₀ : Fin 9) (t : Fin 6), lawAvg honest779 (k + 2) (nearEnv (C := Child) wordDigit k₀ t) =
        (#{p : (Fin (k + 2) → Coords) × Coords | (∀ m, p.1 m ∈ capS 779) ∧
          ListCovExcept wordDigit k₀ t (List.ofFn p.1) p.2} : ENNReal) / ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal)) := by
      intro k₀ t
      have h := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (capS 779) (fun L t' => ListCovExcept wordDigit k₀ t L t')
      rw [card_capS779, card_coords] at h
      exact h
    unfold nearLoad
    simp_rw [hcount, div_eq_mul_inv, ← sum_mul, ← Nat.cast_sum]
    rw [one_pow, one_mul, fNear, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    have hX := hb.trans hle
    calc (54 : ENNReal)⁻¹ * (((∑ k₀ : Fin 9, ∑ t : Fin 6, #{p : (Fin (k + 2) → Coords) × Coords |
            (∀ m, p.1 m ∈ capS 779) ∧ ListCovExcept wordDigit k₀ t (List.ofFn p.1) p.2} : ℕ) : ENNReal) *
              ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal))⁻¹)
        ≤ (54 : ENNReal)⁻¹ * (((nearD.getD (k + 2) 0 : ℕ) : ENNReal) *
              ((J779 : ENNReal) ^ (k + 2) * ((Q ^ 9 : ℕ) : ENNReal))⁻¹) := by
          gcongr
      _ = _ := by
          push_cast
          rw [mul_left_comm, ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
          congr 2
          ring
  · rw [fNear, if_neg hr]
    refine (nearLoad_density r).trans (le_of_eq ?_)
    rw [density_conv r _ (6 * Nn ^ 9) (9 * 128 ^ 9) (by norm_num [Nn]) (by norm_num)]
    congr 3

theorem diag_pay (r : ℕ) :
    lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) ≤
      1 ^ r * ((fDiag r : ENNReal) / ((Q ^ 18 * J779 ^ r : ℕ) : ENNReal)) := by
  by_cases hr : 2 ≤ r ∧ r ≤ 20
  · obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
    have hc := diag_check_all (k + 2) hr.1 hr.2
    unfold diagCheckR at hc
    simp only [Bool.and_eq_true, Nat.ble_eq] at hc
    obtain ⟨hok, hle⟩ := hc
    simp only [Nat.add_sub_cancel] at hok hle
    have hb := ClaudeR3.Asm.diag_bound k 104 (diagRp.getD (k + 2) 0) (2 ^ diagBB.getD (k + 2) 0) (by norm_num)
      (rp_le diagRp k diagRp_le hr.2) hok
    have h := ClaudeR3.Law.lawAvg_uniformOn_count (r := k + 2) (T := Coords × Coords) (capS 779)
      (fun L tt => ListCov wordDigit L tt.1 ∧ ListCov wordDigit L tt.2)
    have henv : (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) =
        fun L => SigGolfResearch.Gate6.Moments.finiteAverage
          (fun tt : Coords × Coords => if ListCov wordDigit L tt.1 ∧ ListCov wordDigit L tt.2 then 1 else 0) := by
      funext L; exact env_sq wordDigit L
    rw [henv, show honest779 = uniformOn (capS 779) from rfl, h, card_capS779, Fintype.card_prod, card_coords, one_pow, one_mul, fDiag, if_pos hr]
    have e779 : capS (675 + 104) = capS 779 := rfl
    rw [e779] at hb
    calc _ ≤ ((diagD.getD (k + 2) 0 : ℕ) : ENNReal) /
          ((J779 : ENNReal) ^ (k + 2) * (((Q ^ 9 * Q ^ 9 : ℕ)) : ENNReal)) :=
          ENNReal.div_le_div_right (by exact_mod_cast hb.trans hle) _
      _ = _ := by push_cast; ring_nf
  · rw [fDiag, if_neg hr]
    have hd := lawAvg_le_uniform honest779 kappa779 honest_density r
      (fun L => env (n := 9) (C := Child) wordDigit L ^ 2)
    rw [env_sq_moment wordDigit (Fintype.card_fin 563) (Fintype.card_fin 128) w1T w2T r,
      density_conv r _ ((Kc * Nn ^ 2) ^ 9) (128 ^ 9) (by norm_num [Kc, Nn]) (by norm_num)] at hd
    refine hd.trans (le_of_eq ?_)
    congr 3

end Pay

end ClaudeR3.Final
end

section
namespace ClaudeR3.Final
open Finset ENNReal
open ClaudeWCT.Numerics.N600 (uniformOn priceN nearPriceN nearLoad priceScale priceScale_mul priceScale_sq_mul
  priceScale_ne_top priceN_ne_top card_index Q A theta_excess_le_square_v5 theta_excess_le_square_54 near_le_sub)
open ClaudeWCT.Numerics.Law (lawAvg marked lawAvg_mul_left lawAvg_sum law_marked_atIndex lawAvg_mono lawAvg_const
  lawAvg_add lawAvg_sum_square_le law_marked_negative_correlation marked_sum_one)
open ClaudeWCT.Numerics.Thinning (env env_le_one env_cons_le nearEnv nearEnv_le_one)
open SphincsSecurity.Concrete (binomialAverage binomialAverage_mul_left)
open SigGolfCandidate.T3.BPORS.History (atIndex)
open ClaudeWCT.Numerics.PoissonReflect (rejection_window_sharp rate_le_one)
open ClaudeWCT.WCT9 (wordDigit Child Rank)
open ClaudeR3.Asm (J779)
open ClaudeR3.PoissonJ (poissonCheckJ poissonCheckJ_sound)

def nearJCheck : Bool := poissonCheckJ J779 13533529 100000000 2 1 fNear (54 * Q ^ 9) (54 * A) 1 259 1 80
def diagJCheck : Bool :=
  poissonCheckJ J779 13533529 100000000 2 1 fDiag (Q ^ 18) (A ^ 2) (2 ^ 31) 3417 1000000 80

theorem meanJ_ok : meanJCheck = true := by decide +kernel
theorem nearJ_ok : nearJCheck = true := by decide +kernel
theorem diagJ_ok : diagJCheck = true := by decide +kernel

theorem lam_window {T : ℕ} (hT2 : T ≤ 2 ^ 32) :
    (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ * 1 ≤ ((2 : ℕ) : ENNReal) / ((1 : ℕ) : ENNReal) := by
  rw [mul_one, Nat.cast_one, div_one]
  calc (T : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ ≤ (2 ^ 32 : ENNReal) * (2 ^ 31 : ENNReal)⁻¹ := by
        gcongr; exact_mod_cast hT2
    _ = 2 := by
        rw [show (2 ^ 32 : ENNReal) = 2 * 2 ^ 31 by norm_num, mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    _ = ((2 : ℕ) : ENNReal) := by norm_num

theorem honest_marked_sum_one : ∑ p, marked (α := Fin (2 ^ 31)) honest779 p = 1 :=
  marked_sum_one honest779 honest_sum_one

theorem diag_pay_one (r : ℕ) : lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2) ≤ 1 :=
  (lawAvg_mono honest779 r fun L => pow_le_one₀ zero_le (env_le_one wordDigit L)).trans_eq
    (lawAvg_const honest779 honest_sum_one r 1)

theorem near_pay_one (r : ℕ) : nearLoad wordDigit (vc := honest779) (C := Child) r ≤ 1 := by
  unfold nearLoad
  calc (54 : ENNReal)⁻¹ * ∑ k : Fin 9, ∑ t : Fin 6, lawAvg honest779 r (nearEnv (C := Child) wordDigit k t)
      ≤ (54 : ENNReal)⁻¹ * ∑ _k : Fin 9, ∑ _t : Fin 6, (1 : ENNReal) :=
        mul_le_mul' le_rfl (sum_le_sum fun k _ => sum_le_sum fun t _ =>
          (lawAvg_mono honest779 r (nearEnv_le_one wordDigit k t)).trans_eq (lawAvg_const honest779 honest_sum_one r 1))
    _ = 1 := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [show ((9 : ℕ) : ENNReal) * (6 : ℕ) = 54 by norm_num, ENNReal.inv_mul_cancel (by simp) (by simp)]

section Window
variable [SampleableType Coords] {T : ℕ} (hT1 : 2 ^ 32 ≤ T) (hT2 : T ≤ 2 ^ 32)
include hT1 hT2

theorem cap_mean_le : lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) ≤ 602 / 1000 := by
  rw [price_mean_eq]
  have h := poissonCheckJ_sound (Dv := J779) (f := fMean) (dbase := Q ^ 9) (sn := A) (sd := 1) (Mn := 602) (Md := 1000)
    meanJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rate_le_one 1 le_rfl
    (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => mean_pay r) (fun r _ => mean_pay_one r)
  simpa only [Nat.cast_one, div_one, Nat.cast_ofNat] using h

theorem cap_diag_eq :
    priceScale ^ 2 * ∑ index : Fin (2 ^ 31), lawAvg (marked (α := Fin (2 ^ 31)) honest779) T
        (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W) ^ 2) =
      (A : ENNReal) ^ 2 / 2 ^ 31 * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T
        (fun r => lawAvg honest779 r (fun L => env (n := 9) (C := Child) wordDigit L ^ 2)) := by
  simp_rw [law_marked_atIndex honest779 honest_sum_one _ T (fun L => env (n := 9) (C := Child) wordDigit L ^ 2),
    card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_sq_mul]

theorem cap_second_le :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W ^ 2) ≤
      lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (priceN wordDigit) ^ 2 + 3417 / 1000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hsq := lawAvg_sum_square_le M T (fun index W => env (n := 9) (C := Child) wordDigit (atIndex index W))
    (fun first second hne => law_marked_negative_correlation honest779 honest_sum_one first second hne T _ _
      (env_cons_le wordDigit) (env_cons_le wordDigit))
  have hmean : lawAvg M T (priceN wordDigit) =
      priceScale * ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W)) := by
    unfold priceN; rw [lawAvg_mul_left, lawAvg_sum]
  have hcheck := poissonCheckJ_sound (Dv := J779) (f := fDiag) (dbase := Q ^ 18) (sn := A ^ 2) (sd := 2 ^ 31)
    (Mn := 3417) (Md := 1000000) diagJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    rate_le_one 1 le_rfl (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => diag_pay r)
    (fun r _ => diag_pay_one r)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hcheck
  calc lawAvg M T (fun W => priceN wordDigit W ^ 2)
      = priceScale ^ 2 * lawAvg M T (fun W => (∑ index : Fin (2 ^ 31),
          env (n := 9) (C := Child) wordDigit (atIndex index W)) ^ 2) := by
        unfold priceN; simp_rw [mul_pow]; rw [lawAvg_mul_left]
    _ ≤ priceScale ^ 2 * ((∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit
          (atIndex index W))) ^ 2 + ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit
          (atIndex index W) ^ 2)) :=
        mul_le_mul' le_rfl hsq
    _ = lawAvg M T (priceN wordDigit) ^ 2 + priceScale ^ 2 *
          ∑ index : Fin (2 ^ 31), lawAvg M T (fun W => env (n := 9) (C := Child) wordDigit (atIndex index W) ^ 2) := by
        rw [hmean]; ring
    _ ≤ _ := by
        rw [cap_diag_eq hT1 hT2]
        exact add_le_add le_rfl hcheck

theorem cap_excess_le :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W - 1023 / 1024) ≤ 2933 / 1000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hmean := cap_mean_le hT1 hT2
  have hsecond := cap_second_le hT1 hT2
  set mean := lawAvg M T (priceN wordDigit)
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × Coords) =>
    theta_excess_le_square_v5 (priceN wordDigit W) mean (priceN_ne_top wordDigit W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_const M honest_marked_sum_one T] at h
  have hcancel : (1588 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024) ≤ 3417 / 1000000 := by
    have hmt : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hmt))
    calc
      _ = (1588 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN wordDigit W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3417 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 1588 : ENNReal) * (1588 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 1588 : ENNReal) * ((1588 / 1000) * lawAvg M T (fun W => priceN wordDigit W - 1023 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 1588 : ENNReal) * (3417 / 1000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

theorem cap_excess_le_54 :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (fun W => priceN wordDigit W - 2031 / 1024) ≤ 6186 / 10000000 := by
  set M := marked (α := Fin (2 ^ 31)) honest779
  have hmean := cap_mean_le hT1 hT2
  have hsecond := cap_second_le hT1 hT2
  set mean := lawAvg M T (priceN wordDigit)
  have h := lawAvg_mono M T (fun W : List (Fin (2 ^ 31) × Coords) =>
    theta_excess_le_square_54 (priceN wordDigit W) mean (priceN_ne_top wordDigit W) hmean)
  rw [lawAvg_add, lawAvg_add, lawAvg_mul_left, lawAvg_mul_left, lawAvg_const M honest_marked_sum_one T] at h
  have hcancel : (5524 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024) ≤ 3417 / 1000000 := by
    have hmt : mean ≠ ⊤ := ne_top_of_le_ne_top (by finiteness) hmean
    apply ENNReal.le_of_add_le_add_right (a := 2 * mean ^ 2) (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hmt))
    calc
      _ = (5524 / 1000 : ENNReal) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024) + 2 * mean * mean := by ring
      _ ≤ lawAvg M T (fun W => priceN wordDigit W ^ 2) + mean ^ 2 := h
      _ ≤ (mean ^ 2 + 3417 / 1000000) + mean ^ 2 := add_le_add hsecond le_rfl
      _ = _ := by ring
  have hi : (1000 / 5524 : ENNReal) * (5524 / 1000) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
  calc
    _ = (1000 / 5524 : ENNReal) * ((5524 / 1000) * lawAvg M T (fun W => priceN wordDigit W - 2031 / 1024)) := by
        rw [← mul_assoc, hi, one_mul]
    _ ≤ (1000 / 5524 : ENNReal) * (3417 / 1000000) := mul_le_mul' le_rfl hcancel
    _ ≤ _ := by
        apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

theorem cap_nearPrice_eq :
    lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (nearPriceN wordDigit) =
      54 * (A : ENNReal) * binomialAverage (2 ^ 31 : ENNReal)⁻¹ T (nearLoad wordDigit (vc := honest779) (C := Child)) := by
  unfold nearPriceN nearLoad
  rw [lawAvg_mul_left, lawAvg_sum]
  simp_rw [lawAvg_sum, law_marked_atIndex honest779 honest_sum_one, card_index]
  rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← priceScale_mul,
    binomialAverage_mul_left]
  simp_rw [← SphincsSecurity.Concrete.binomialAverage_sum]
  have h : (54 : ENNReal) * 54⁻¹ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  rw [← mul_assoc, show (54 : ENNReal) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) * 54⁻¹ =
    (54 * 54⁻¹) * (priceScale * ((2 ^ 31 : ℕ) : ENNReal)) by ring, h, one_mul]

theorem cap_near_le : lawAvg (marked (α := Fin (2 ^ 31)) honest779) T (nearPriceN wordDigit) ≤ 300 - 1 / 16 := by
  rw [cap_nearPrice_eq hT1 hT2]
  have h := poissonCheckJ_sound (Dv := J779) (f := fNear) (dbase := 54 * Q ^ 9) (sn := 54 * A) (sd := 1) (Mn := 259)
    (Md := 1) nearJ_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rate_le_one 1 le_rfl
    (lam_window hT2) (rejection_window_sharp T hT1) _ (fun r _ => near_pay r) (fun r _ => near_pay_one r)
  simp only [Nat.cast_one, div_one, Nat.cast_ofNat, Nat.cast_mul] at h
  exact h.trans (by simpa only [div_one] using near_le_sub)

end Window

end ClaudeR3.Final
end
