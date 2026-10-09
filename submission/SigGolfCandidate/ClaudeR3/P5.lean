import SigGolfCandidate.ClaudeR3.P4

namespace ClaudeR3.KEval
open Finset
open ClaudeR3.Poly
open ClaudeR3.Tab (digit extCount levs sum_child lev Tab)
open ClaudeWCT.WCT9 (childExtra Child Rank)

section
variable {R : Type*} [CommRing R]

def rsum (n : ℕ) (f : ℕ → R) : R := (List.range n).foldr (fun i s => f i + s) 0

theorem rsum_eq (n : ℕ) (f : ℕ → R) : rsum n f = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rsum, List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil, add_zero]
    have hshift : ∀ (l : List ℕ) (c : R), l.foldr (fun i s => f i + s) c = l.foldr (fun i s => f i + s) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons a l ihl => simp only [List.foldr_cons, ihl]; ring
    rw [hshift, ← rsum, ih]

def rhoI (key : ℕ) (x : R) : R := rsum 15 fun l => (digit key l : R) * x ^ l
def dsumI (key : ℕ) : R := rsum 15 fun l => (digit key l : R)
def RtI (x : R) : R := (levs.map fun l => x ^ l).sum
def EtI (x : R) : R := rsum 4 fun e => (extCount e : R) * x ^ e
def AI (e : ℕ) (x : R) : R := (EtI x - x ^ e) * RtI x

theorem Rt_eval (x : R) : Rt x = RtI x := by
  unfold Rt RtI
  rw [← List.ofFn_getElem (xs := levs), List.map_ofFn, List.sum_ofFn]
  refine Fintype.sum_equiv (finCongr ClaudeR3.Tab.levs_length.symm) _ _ fun b => ?_
  simp only [Function.comp, finCongr_apply, Fin.coe_cast]
  rw [ClaudeR3.Tab.levs_get]

theorem Et_eval (x : R) : Et x = EtI x := by
  unfold Et EtI
  rw [rsum_eq, sum_child (fun e => x ^ e)]
  simp [nsmul_eq_mul]

theorem rhoK_eval (key : ℕ) (x : R) : rhoK key x = rhoI key x := by
  unfold rhoK rhoI
  rw [rsum_eq]

theorem LamP_eval (e key : ℕ) (x : R) : LamP e key x = AI e x + x ^ e * rhoI key x := by
  unfold LamP AI
  rw [Rt_eval, Et_eval, rhoK_eval]

theorem EtI_one : EtI (1 : R) = 128 := by
  have h := ClaudeR3.Tab.extCount_vals
  rw [EtI, rsum_eq]
  simp [Finset.sum_range_succ, h.1, h.2.1, h.2.2.1, h.2.2.2]
  norm_num

theorem RtI_one : RtI (1 : R) = 563 := by
  simp only [RtI, one_pow]
  rw [List.map_const', List.sum_replicate, ClaudeR3.Tab.levs_length, nsmul_eq_mul, mul_one]
  norm_num

theorem rhoI_one (key : ℕ) : rhoI key (1 : R) = dsumI key := by
  simp [rhoI, dsumI]

theorem LamP_eval_one (e key : ℕ) : LamP e key (1 : R) = 71501 + dsumI key := by
  rw [LamP_eval]
  unfold AI
  rw [EtI_one, RtI_one, rhoI_one]
  ring

theorem lam3_eval (k L e key : ℕ) (x : R) :
    lam3 k L e key x =
      (AI e x + x ^ e * rhoI key x) * (AI e (x ^ L) + (x ^ L) ^ e * rhoI key (x ^ L)) * (71501 + dsumI key) ^ k := by
  unfold lam3
  rw [LamP_eval_one, LamP_eval, LamP_eval]

theorem Psi_eval (k L key : ℕ) (x : R) :
    Psi k L key x = ∑ e ∈ range 4, (extCount e : R) *
      ((AI e x + x ^ e * rhoI key x) * (AI e (x ^ L) + (x ^ L) ^ e * rhoI key (x ^ L)) *
        (71501 + dsumI key) ^ k) := by
  unfold Psi
  rw [sum_child (fun e => lam3 k L e key x)]
  refine sum_congr rfl fun e _ => ?_
  rw [nsmul_eq_mul, lam3_eval]

abbrev Rec := ℕ × ℤ

theorem list_sum_finset {ι : Type*} (l : List Rec) (s : Finset ι) (f : Rec → ι → R) :
    (l.map fun a => ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sum_add_distrib]

structure Sums (R : Type*) where
  s0 : R
  s1x : R
  s1y : R
  s2 : R

def alphaI (k : ℕ) (a : Rec) : R := (a.2 : R) * (71501 + dsumI a.1) ^ k

def sums (tab : Tab) (k : ℕ) (x y : R) : Sums R where
  s0 := (tab.map fun a => alphaI k a).sum
  s1x := (tab.map fun a => alphaI k a * rhoI a.1 x).sum
  s1y := rsum 15 fun l => y ^ l * (tab.map fun a => alphaI k a * (digit a.1 l : R)).sum
  s2 := rsum 15 fun l => y ^ l * (tab.map fun a => alphaI k a * (digit a.1 l : R) * rhoI a.1 x).sum

def combine (S : Sums R) (x y : R) : R :=
  rsum 4 fun e => (extCount e : R) *
    (AI e x * AI e y * S.s0 + AI e x * y ^ e * S.s1y + x ^ e * AI e y * S.s1x + x ^ e * y ^ e * S.s2)

def famEval (tab : Tab) (k L : ℕ) (x : R) : R := combine (sums tab k x (x ^ L)) x (x ^ L)

theorem rhoI_y (key : ℕ) (y : R) : rhoI key y = ∑ l ∈ range 15, (digit key l : R) * y ^ l := by
  rw [rhoI, rsum_eq]

theorem per_rec (k L : ℕ) (x : R) (a : Rec) :
    ((a.2 : ℤ) : R) * Psi k L a.1 x = ∑ e ∈ range 4, (extCount e : R) *
      (AI e x * AI e (x ^ L) * alphaI k a
        + AI e x * (x ^ L) ^ e * (∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R)))
        + x ^ e * AI e (x ^ L) * (alphaI k a * rhoI a.1 x)
        + x ^ e * (x ^ L) ^ e * (∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R) * rhoI a.1 x))) := by
  rw [Psi_eval, mul_sum]
  refine sum_congr rfl fun e _ => ?_
  have hA : ∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R)) = alphaI k a * rhoI a.1 (x ^ L) := by
    rw [rhoI_y, mul_sum]; exact sum_congr rfl fun l _ => by ring
  have hB : ∑ l ∈ range 15, (x ^ L) ^ l * (alphaI k a * (digit a.1 l : R) * rhoI a.1 x) =
      alphaI k a * rhoI a.1 x * rhoI a.1 (x ^ L) := by
    rw [rhoI_y a.1 (x ^ L), mul_sum]; exact sum_congr rfl fun l _ => by ring
  rw [hA, hB, alphaI]
  ring

theorem list_sum_mul_left (l : List Rec) (c : R) (f : Rec → R) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, mul_add]

theorem list_sum_add (l : List Rec) (f g : Rec → R) :
    (l.map fun a => f a + g a).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]; ring

theorem famEval_eq (tab : Tab) (k L : ℕ) (x : R) : tabSum tab (fun key => Psi k L key x) = famEval tab k L x := by
  unfold tabSum
  simp_rw [per_rec k L x]
  rw [list_sum_finset]
  unfold famEval combine
  rw [rsum_eq]
  refine sum_congr rfl fun e _ => ?_
  rw [list_sum_mul_left, list_sum_add, list_sum_add, list_sum_add, list_sum_mul_left, list_sum_mul_left,
    list_sum_mul_left, list_sum_mul_left, list_sum_finset, list_sum_finset]
  simp only [sums, rsum_eq, list_sum_mul_left]

end

end ClaudeR3.KEval
