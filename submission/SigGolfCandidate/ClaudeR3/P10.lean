import SigGolfCandidate.ClaudeR3.P9
import SigGolfCandidate.ClaudeR3.E1
import SigGolfCandidate.ClaudeR3.K1
import SigGolfCandidate.ClaudeR3.K2
import SigGolfCandidate.ClaudeR3.K3
import SigGolfCandidate.ClaudeR3.K4
import SigGolfCandidate.ClaudeR3.E3

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
