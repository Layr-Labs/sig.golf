import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.Pi

-- ==== merged from ClaudeWCT_Numerics_Kernel ====
section

namespace ClaudeWCT.Numerics.Kernel
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n
def PB : Nat := 2 ^ 64
def HB : Nat := 2 ^ 128
def monos (js : List Nat) : Nat := js.foldr (fun j s => PB ^ j + s) 0
def box (m : Nat) : Nat := monos (List.range (m + 1))
def chainFac (inS : Bool) (x : Nat) : Nat :=
  if inS then (match x with | 0 => 0 | x' + 1 => box x') else box 3
def pairFac (x : Nat) : Nat :=
  monos ((List.range (x + 1)).map (fun b => x + 32 * b) ++ (List.range x).map (fun a => a + 32 * x))
def coeffAt (p j : Nat) : Nat := p / PB ^ j % PB
abbrev Opt := Nat × Nat × Nat × Bool
def loopK (child : Nat → Nat → Nat → Nat → Nat → Bool → Nat × Nat) (n rem u fu fb fden : Nat)
    (inS : Bool) : (j k : Nat) → (q p fk : Nat) → (sg : Bool) → Nat × Nat
  | 0, _, _, _, _, _ => (0, 0)
  | j + 1, k, q, p, fk, sg =>
    if k * u ≤ rem then
      let a := child (n - k) (rem - k * u) q p (fden * fk) sg
      let b := loopK child n rem u fu fb fden inS j (k + 1) (q * fb) (p * fu) (fk * (k + 1)) (sg ^^ inS)
      (a.1 + b.1, a.2 + b.2)
    else (0, 0)
def enumK (hb total qIdx : Nat) : (opts : List Opt) → (n rem : Nat) → (q p fden : Nat) → (neg : Bool) →
    Nat × Nat
  | [], n, rem, q, p, fden, neg =>
    if n == 0 && rem == 0 then
      let h := (fact total / fden) * coeffAt q qIdx * hb ^ coeffAt p 6
      if neg then (0, h) else (h, 0)
    else (0, 0)
  | (u, fu, fb, inS) :: os, n, rem, q, p, fden, neg =>
    loopK (fun n' rem' q' p' fden' sg => enumK hb total qIdx os n' rem' q' p' fden' sg)
      n rem u fu fb fden inS (n + 1) 0 q p 1 neg
def optsU : List Opt :=
  [(0, chainFac false 0, 1, false), (0, chainFac true 0, 1, true),
   (1, chainFac false 1, 1, false), (1, chainFac true 1, 1, true),
   (2, chainFac false 2, 1, false), (2, chainFac true 2, 1, true),
   (3, chainFac false 3, 1, false), (3, chainFac true 3, 1, true)]
def optsP : List Opt :=
  [(0, chainFac false 0, pairFac 0, false), (0, chainFac true 0, pairFac 0, true),
   (0, chainFac false 1, pairFac 1, false), (0, chainFac true 1, pairFac 1, true),
   (0, chainFac false 2, pairFac 2, false), (0, chainFac true 2, pairFac 2, true),
   (0, chainFac false 3, pairFac 3, false), (0, chainFac true 3, pairFac 3, true)]
def w1Hist (hb : Nat) : Nat × Nat := enumK hb 7 0 optsU 7 6 1 1 1 false
def wfHist (hb : Nat) : Nat × Nat :=
  (List.range 4).foldr (fun x acc =>
    let h := enumK hb 6 0 optsU 6 (6 - x) 1 (box 3) 1 false
    (h.1 + acc.1, h.2 + acc.2)) (0, 0)
def w2Hist (hb : Nat) : Nat × Nat := enumK hb 7 (6 + 32 * 6) optsP 7 0 1 1 1 false
def packPos (d : List (Nat × Int)) : Nat := d.foldr (fun e s => e.2.toNat * HB ^ e.1 + s) 0
def packNeg (d : List (Nat × Int)) : Nat := d.foldr (fun e s => (-e.2).toNat * HB ^ e.1 + s) 0
def histEq (h : Nat × Nat) (d : List (Nat × Int)) : Bool := h.1 + packNeg d == h.2 + packPos d
def massOk (m : Nat × Nat) (d : List (Nat × Int)) : Bool :=
  m.1 < 2 ^ 120 && m.2 < 2 ^ 120 && packPos' d < 2 ^ 120 && packNeg' d < 2 ^ 120
where
  packPos' (d : List (Nat × Int)) : Nat := d.foldr (fun e s => e.2.toNat + s) 0
  packNeg' (d : List (Nat × Int)) : Nat := d.foldr (fun e s => (-e.2).toNat + s) 0
def w1Data : List (Nat × Int) := [(0, 7), (1, -42), (3, -105), (10, 210), (22, 420), (34, 140), (44, -700), (46, 210), (84, -1050), (115, -420), (135, 1365), (155, -420), (206, -210), (236, 1470), (277, -35), (301, 630), (336, -1512), (402, 315), (502, 210), (552, -840), (617, 21), (672, -392), (728, 728)]
def wfData : List (Nat × Int) := [(0, 1), (1, -12), (3, -30), (10, 90), (22, 180), (34, 60), (44, -400), (46, 90), (84, -600), (115, -240), (135, 975), (155, -240), (206, -120), (236, 1050), (277, -20), (301, 450), (336, -1296), (402, 225), (502, 150), (552, -720), (617, 15), (672, -336), (728, 728)]
def w2Data : List (Nat × Int) := [(0, 122073), (1, 157892), (3, -267855), (4, 105840), (5, 32970), (6, -200340), (8, -511560), (9, 26040), (10, 279300), (12, 31080), (15, -511560), (16, 3360), (17, 840), (20, -333480), (22, 1076460), (23, 6300), (25, -107100), (31, 1680), (34, 284340), (42, 140), (44, -836010), (46, 1194690), (53, -110880), (68, 1236480), (72, -85680), (78, -5040), (84, -2182110), (92, 522480), (96, 249060), (98, -5670), (106, -27720), (115, -1251600), (130, 617400), (135, 1437177), (144, -4200), (149, -2520), (155, -1592640), (176, 64470), (177, 203280), (202, -420), (206, -1533630), (234, 12600), (236, 2330790), (239, 73640), (267, -306810), (277, -318675), (301, 1277010), (315, 27300), (336, -1342656), (358, -374850), (402, 803985), (405, 4200), (453, -133350), (502, 764190), (510, 210), (552, -1028160), (563, -11550), (617, 157605), (672, -548800), (728, 529984)]
def wpos (d : List (Nat × Int)) (base r : Nat) : Nat := d.foldr (fun e s => e.2.toNat * (base + e.1) ^ r + s) 0
def wneg (d : List (Nat × Int)) (base r : Nat) : Nat := d.foldr (fun e s => (-e.2).toNat * (base + e.1) ^ r + s) 0
def wwpos (d : List (Nat × Int)) (base r : Nat) : Nat :=
  d.foldr (fun e s => e.2.toNat * wpos d (base + e.1) r + (-e.2).toNat * wneg d (base + e.1) r + s) 0
def wwneg (d : List (Nat × Int)) (base r : Nat) : Nat :=
  d.foldr (fun e s => e.2.toNat * wneg d (base + e.1) r + (-e.2).toNat * wpos d (base + e.1) r + s) 0
def Nn : Nat := 728
def Kc : Nat := 128
def Q : Nat := 93184
def B1 : Nat := 92456
def B2 : Nat := 91728
def xNum (r : Nat) : Nat := wpos w1Data B1 r - wneg w1Data B1 r
def xOk (r : Nat) : Bool := wneg w1Data B1 r ≤ wpos w1Data B1 r
def xfNum (r : Nat) : Nat := wpos wfData B1 r - wneg wfData B1 r
def xfOk (r : Nat) : Bool := wneg wfData B1 r ≤ wpos wfData B1 r
def yPos (r : Nat) : Nat := wpos w2Data B1 r + (Kc - 1) * wwpos w1Data B2 r
def yNeg (r : Nat) : Nat := wneg w2Data B1 r + (Kc - 1) * wwneg w1Data B2 r
def yNum (r : Nat) : Nat := yPos r - yNeg r
def yOk (r : Nat) : Bool := yNeg r ≤ yPos r
def poissonCheck (f : Nat → Nat) (ok : Nat → Bool) (dbase sn sd Mn Md R : Nat) : Bool :=
  let S := (List.range (R + 1)).foldr (fun r s =>
    27 * 513 ^ r * 256 ^ (R - r) * (fact R / fact r) * f r * Q ^ (9 * (R - r)) + s) 0
  (List.range (R + 1)).all ok &&
  Md * sn * (S * 256 * (R + 1) + 513 ^ (R + 1) * 200 * dbase * Q ^ (9 * R)) ≤
    Mn * sd * 200 * dbase * 256 ^ (R + 1) * fact (R + 1) * Q ^ (9 * R)
def A : Nat := 2 ^ 26 * 1001 ^ 9
def meanCheck : Bool := poissonCheck (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 37 64 80
def meanTightCheck : Bool := poissonCheck (fun r => xNum r ^ 9) xOk (Nn ^ 9) A 1 1 10 80
def nearCheck : Bool :=
  poissonCheck (fun r => xNum r ^ 8 * xfNum r) (fun r => xOk r && xfOk r) (Nn ^ 9) (63 * A) 1 404 1 80
def diagCheck : Bool :=
  poissonCheck (fun r => yNum r ^ 9) yOk ((Kc * Nn ^ 2) ^ 9) (A ^ 2) (2 ^ 31) 18400 100000000 80
end ClaudeWCT.Numerics.Kernel
end
-- ==== merged from ClaudeWCT_Numerics_CoverW1 ====
section

section
namespace ClaudeWCT.Numerics.Kernel
open Finset
theorem fact_eq : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by rw [fact, fact_eq n, Nat.factorial_succ]
def signedPair (b : Bool) (h : ℕ) : ℕ × ℕ := if b then (0, h) else (h, 0)
theorem loopK_eq (child : ℕ → ℕ → ℕ → ℕ → ℕ → Bool → ℕ × ℕ) (n rem u fu fb fden q0 p0 : ℕ)
    (inS neg : Bool) :
    ∀ (j k : ℕ), loopK child n rem u fu fb fden inS j k (q0 * fb ^ k) (p0 * fu ^ k) k.factorial
        (neg ^^ (inS && k % 2 == 1)) =
      ∑ i ∈ range j, (if (k + i) * u ≤ rem then
        child (n - (k + i)) (rem - (k + i) * u) (q0 * fb ^ (k + i)) (p0 * fu ^ (k + i))
          (fden * (k + i).factorial) (neg ^^ (inS && (k + i) % 2 == 1)) else 0)
  | 0, k => by simp [loopK]
  | j + 1, k => by
    by_cases hk : k * u ≤ rem
    · rw [sum_range_succ']
      have ih := loopK_eq child n rem u fu fb fden q0 p0 inS neg j (k + 1)
      simp only [loopK, if_pos hk, add_zero]
      have hq : q0 * fb ^ k * fb = q0 * fb ^ (k + 1) := by rw [pow_succ, mul_assoc]
      have hp : p0 * fu ^ k * fu = p0 * fu ^ (k + 1) := by rw [pow_succ, mul_assoc]
      have hf : k.factorial * (k + 1) = (k + 1).factorial := by
        rw [Nat.factorial_succ, mul_comm]
      have hs : ((neg ^^ (inS && k % 2 == 1)) ^^ inS) = (neg ^^ (inS && (k + 1) % 2 == 1)) := by
        rcases Nat.mod_two_eq_zero_or_one k with h | h <;>
          cases inS <;> cases neg <;> simp [h, Nat.succ_mod_two_eq_one_iff]
      rw [hq, hp, hf, hs, ih, ← Prod.mk_add_mk, Prod.mk.eta, Prod.mk.eta, add_comm]
      congr 1
      refine sum_congr rfl fun i _ => ?_
      rw [show k + 1 + i = k + (i + 1) by omega]
    · simp only [loopK, if_neg hk]
      symm
      refine sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact hk (le_trans (Nat.mul_le_mul_right u (Nat.le_add_right k _)) h)
def term (hb total qIdx : ℕ) : (opts : List Opt) → (Fin opts.length → ℕ) → (rem q p fden : ℕ) →
    (neg : Bool) → ℕ × ℕ
  | [], _, rem, q, p, fden, neg =>
    if rem = 0 then signedPair neg ((fact total / fden) * coeffAt q qIdx * hb ^ coeffAt p 6) else 0
  | (u, fu, fb, inS) :: os, k, rem, q, p, fden, neg =>
    if k 0 * u ≤ rem then
      term hb total qIdx os (Fin.tail k) (rem - k 0 * u) (q * fb ^ k 0) (p * fu ^ k 0)
        (fden * (k 0).factorial) (neg ^^ (inS && k 0 % 2 == 1))
    else 0
theorem sum_antidiagonalTuple_succ {M : Type*} [AddCommMonoid M] (m n : ℕ) (f : (Fin (m + 1) → ℕ) → M) :
    ∑ x ∈ Nat.antidiagonalTuple (m + 1) n, f x =
      ∑ i ∈ range (n + 1), ∑ y ∈ Nat.antidiagonalTuple m (n - i), f (Fin.cons i y) := by
  rw [sum_sigma']
  refine sum_bij' (fun x _ => ⟨x 0, Fin.tail x⟩) (fun s _ => Fin.cons s.1 s.2) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ] at hx
    simp only [mem_sigma, mem_range, Nat.mem_antidiagonalTuple]
    refine ⟨by omega, ?_⟩
    simp only [Fin.tail]
    omega
  · intro s hs
    simp only [mem_sigma, mem_range, Nat.mem_antidiagonalTuple] at hs
    rw [Nat.mem_antidiagonalTuple, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    omega
  · intro x _; exact Fin.cons_self_tail x
  · intro s _; simp
  · intro x _; simp
theorem enumK_eq (hb total qIdx : ℕ) : ∀ (opts : List Opt) (n rem q p fden : ℕ) (neg : Bool),
    enumK hb total qIdx opts n rem q p fden neg =
      ∑ k ∈ Nat.antidiagonalTuple opts.length n, term hb total qIdx opts k rem q p fden neg
  | [], n, rem, q, p, fden, neg => by
    cases n with
    | zero =>
      simp only [enumK, List.length_nil, Nat.antidiagonalTuple_zero_zero, sum_singleton, term]
      by_cases h : rem = 0
      · simp [h, signedPair]
      · simp [h]
    | succ n =>
      simp [enumK, Nat.antidiagonalTuple_zero_succ]
  | (u, fu, fb, inS) :: os, n, rem, q, p, fden, neg => by
    have hl := loopK_eq (fun n' rem' q' p' fden' sg => enumK hb total qIdx os n' rem' q' p' fden' sg)
      n rem u fu fb fden q p inS neg (n + 1) 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.zero_mod, Nat.reduceBEq,
      Bool.and_false, Bool.xor_false, zero_add] at hl
    simp only [enumK, List.length_cons]
    rw [hl, sum_antidiagonalTuple_succ]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [term, Fin.cons_zero, Fin.tail_cons]
    by_cases h : i * u ≤ rem
    · simp only [if_pos h]
      rw [enumK_eq hb total qIdx os]
    · simp only [if_neg h, sum_const_zero]
end ClaudeWCT.Numerics.Kernel
end
section
namespace ClaudeWCT.Numerics
open Polynomial
theorem eval_eq_coeff_zero_add (f : ℕ[X]) (B : ℕ) : f.eval B = f.coeff 0 + B * f.divX.eval B := by
  conv_lhs => rw [← divX_mul_X_add f]
  simp only [eval_add, eval_mul, eval_X, eval_C]
  ring
theorem eval_div_pow_mod {B : ℕ} (hB : 0 < B) :
    ∀ (j : ℕ) (f : ℕ[X]), (∀ i, f.coeff i < B) → f.eval B / B ^ j % B = f.coeff j
  | 0, f, h => by
    rw [eval_eq_coeff_zero_add, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (h 0)]
  | j + 1, f, h => by
    have hd : ∀ i, f.divX.coeff i < B := fun i => by rw [coeff_divX]; exact h _
    rw [eval_eq_coeff_zero_add, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hB,
      Nat.div_eq_of_lt (h 0), zero_add, eval_div_pow_mod hB j f.divX hd, coeff_divX]
theorem eq_of_eval_eq {B : ℕ} (hB : 0 < B) {f g : ℕ[X]} (hf : ∀ i, f.coeff i < B)
    (hg : ∀ i, g.coeff i < B) (h : f.eval B = g.eval B) : f = g := by
  ext j
  rw [← eval_div_pow_mod hB j f hf, ← eval_div_pow_mod hB j g hg, h]
theorem coeff_le_eval_one (f : ℕ[X]) (i : ℕ) : f.coeff i ≤ f.eval 1 := by
  rw [eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one]
  by_cases hi : i ∈ f.support
  · exact Finset.single_le_sum (f := fun e => f.coeff e) (fun _ _ => Nat.zero_le _) hi
  · rw [Polynomial.notMem_support_iff.mp hi]; exact Nat.zero_le _
end ClaudeWCT.Numerics
end
section
namespace ClaudeWCT.Numerics.Kernel
open Finset Polynomial
variable {ι : Type*}
def histOf (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool) (amt cnt : ι → ℕ)
    (hb : ℕ) : ℕ × ℕ :=
  ∑ i ∈ T, if cond i then signedPair (sgn i) (amt i * hb ^ cnt i) else 0
noncomputable def histPoly (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool)
    (amt cnt : ι → ℕ) (b : Bool) : ℕ[X] :=
  ∑ i ∈ T, if cond i ∧ sgn i = b then C (amt i) * X ^ cnt i else 0
theorem histOf_eq (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool)
    (amt cnt : ι → ℕ) (hb : ℕ) :
    histOf T cond sgn amt cnt hb =
      ((histPoly T cond sgn amt cnt false).eval (hb : ℕ), (histPoly T cond sgn amt cnt true).eval hb) := by
  unfold histOf histPoly
  set g : ι → ℕ × ℕ := fun i => if cond i then signedPair (sgn i) (amt i * hb ^ cnt i) else 0 with hg
  ext
  · simp only [Prod.fst_sum, eval_finsetSum]
    refine sum_congr rfl fun i _ => ?_
    by_cases hc : cond i <;> cases hs : sgn i <;> simp [hg, hc, hs, signedPair]
  · simp only [Prod.snd_sum, eval_finsetSum]
    refine sum_congr rfl fun i _ => ?_
    by_cases hc : cond i <;> cases hs : sgn i <;> simp [hg, hc, hs, signedPair]
noncomputable def dataPoly (d : List (ℕ × ℤ)) (b : Bool) : ℕ[X] :=
  d.foldr (fun e s => C (if b then (-e.2).toNat else e.2.toNat) * X ^ e.1 + s) 0
theorem packPos_eq (d : List (ℕ × ℤ)) : packPos d = (dataPoly d false).eval HB := by
  induction d with
  | nil => simp [packPos, dataPoly]
  | cons e d ih =>
    simp only [packPos, dataPoly, List.foldr_cons] at ih ⊢
    rw [ih]; simp
theorem packNeg_eq (d : List (ℕ × ℤ)) : packNeg d = (dataPoly d true).eval HB := by
  induction d with
  | nil => simp [packNeg, dataPoly]
  | cons e d ih =>
    simp only [packNeg, dataPoly, List.foldr_cons] at ih ⊢
    rw [ih]; simp
theorem packPos'_eq (d : List (ℕ × ℤ)) : massOk.packPos' d = (dataPoly d false).eval 1 := by
  induction d with
  | nil => simp [massOk.packPos', dataPoly]
  | cons e d ih =>
    simp only [massOk.packPos', dataPoly, List.foldr_cons] at ih ⊢
    rw [ih]; simp
theorem packNeg'_eq (d : List (ℕ × ℤ)) : massOk.packNeg' d = (dataPoly d true).eval 1 := by
  induction d with
  | nil => simp [massOk.packNeg', dataPoly]
  | cons e d ih =>
    simp only [massOk.packNeg', dataPoly, List.foldr_cons] at ih ⊢
    rw [ih]; simp
noncomputable def powSum (p : ℕ) : ℕ[X] →+ ℤ where
  toFun f := f.sum (fun j a => (a : ℤ) * (j : ℤ) ^ p)
  map_zero' := by simp
  map_add' f g := Polynomial.sum_add_index (S := ℤ) f g (fun j a => (a : ℤ) * (j : ℤ) ^ p) (fun _ => by simp)
    (fun _ _ _ => by push_cast; ring)
theorem powSum_monomial (p a c : ℕ) : powSum p (C a * X ^ c) = (a : ℤ) * (c : ℤ) ^ p := by
  show (C a * X ^ c).sum (fun j b => (b : ℤ) * (j : ℤ) ^ p) = _
  rw [C_mul_X_pow_eq_monomial, sum_monomial_index]
  simp
theorem powSum_natCast_monomial (p a c : ℕ) : powSum p ((a : ℕ[X]) * X ^ c) = (a : ℤ) * (c : ℤ) ^ p := by
  rw [← powSum_monomial, ← Polynomial.C_eq_natCast, Nat.cast_id]
theorem powSum_data (p : ℕ) (d : List (ℕ × ℤ)) :
    powSum p (dataPoly d false) - powSum p (dataPoly d true) = (d.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  induction d with
  | nil => simp [dataPoly]
  | cons e d ih =>
    simp only [dataPoly, List.foldr_cons, map_add, Bool.false_eq_true, if_false, if_true,
      List.map_cons, List.sum_cons] at ih ⊢
    rw [powSum_monomial, powSum_monomial, ← ih]
    have h := Int.toNat_sub_toNat_neg e.2
    linear_combination (e.1 : ℤ) ^ p * h
theorem coeff_lt_of_eval_one {f : ℕ[X]} (h : f.eval 1 < 2 ^ 127) (j : ℕ) : f.coeff j < HB := by
  have := coeff_le_eval_one f j
  unfold HB
  omega
theorem decode (T : Finset ι) (cond : ι → Prop) [DecidablePred cond] (sgn : ι → Bool) (amt cnt : ι → ℕ)
    (d : List (ℕ × ℤ)) (hEq : histEq (histOf T cond sgn amt cnt HB) d = true)
    (hMass : massOk (histOf T cond sgn amt cnt 1) d = true) (p : ℕ) :
    ∑ i ∈ T, (if cond i then (if sgn i then (-1 : ℤ) else 1) * amt i * (cnt i : ℤ) ^ p else 0) =
      (d.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  unfold massOk at hMass
  rw [histOf_eq, packPos'_eq, packNeg'_eq] at hMass
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hMass
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hMass
  have hE : (histPoly T cond sgn amt cnt false + dataPoly d true).eval HB =
      (histPoly T cond sgn amt cnt true + dataPoly d false).eval HB := by
    unfold histEq at hEq
    rw [histOf_eq, packNeg_eq, packPos_eq] at hEq
    simpa [eval_add] using hEq
  have hHB : 0 < HB := by unfold HB; positivity
  have hpoly : histPoly T cond sgn amt cnt false + dataPoly d true =
      histPoly T cond sgn amt cnt true + dataPoly d false := by
    refine eq_of_eval_eq hHB (fun j => coeff_lt_of_eval_one ?_ j) (fun j => coeff_lt_of_eval_one ?_ j) hE
    · rw [eval_add]; omega
    · rw [eval_add]; omega
  have hL := congrArg (powSum p) hpoly
  rw [map_add, map_add] at hL
  have hD := powSum_data p d
  have hH : powSum p (histPoly T cond sgn amt cnt false) - powSum p (histPoly T cond sgn amt cnt true) =
      ∑ i ∈ T, (if cond i then (if sgn i then (-1 : ℤ) else 1) * amt i * (cnt i : ℤ) ^ p else 0) := by
    simp only [histPoly, map_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases hc : cond i <;> cases hs : sgn i <;> simp [hc, powSum_natCast_monomial]
  rw [← hH, ← hD]
  linarith
end ClaudeWCT.Numerics.Kernel
end
section
namespace ClaudeWCT.Numerics
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
def occ {n : ℕ} (o : Fin n → α) (a : α) : ℕ := #{i | o i = a}
theorem occ_sum {n : ℕ} (o : Fin n → α) : ∑ a, occ o a = n := by
  unfold occ
  rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (o i)), card_univ, Fintype.card_fin]
theorem occ_mem_piAntidiag {n : ℕ} (o : Fin n → α) : occ o ∈ piAntidiag univ n := by
  rw [mem_piAntidiag]
  exact ⟨occ_sum o, fun a _ => mem_univ a⟩
theorem prod_X_eq_monomial {n : ℕ} (o : Fin n → α) :
    ∏ i, (MvPolynomial.X (o i) : MvPolynomial α ℕ) =
      MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (occ o)) 1 := by
  rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_one, one_mul]
  rw [← prod_fiberwise (s := univ) (g := o) (f := fun i => (MvPolynomial.X (o i) : MvPolynomial α ℕ))]
  refine prod_congr rfl fun a _ => ?_
  rw [prod_congr rfl (g := fun _ => (MvPolynomial.X a : MvPolynomial α ℕ)) (fun i hi => by
    rw [(mem_filter.mp hi).2]), prod_const]
  rfl
theorem card_occ_eq {n : ℕ} (k : α → ℕ) (hk : k ∈ piAntidiag univ n) :
    #{o : Fin n → α | occ o = k} = Nat.multinomial univ k := by
  have key := sum_pow_eq_sum_piAntidiag (R := MvPolynomial α ℕ) univ (fun a => MvPolynomial.X a) n
  rw [Fintype.sum_pow] at key
  simp_rw [prod_X_eq_monomial] at key
  have hc := congrArg (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm k)) key
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at hc
  have hl : (∑ x : Fin n → α, if Finsupp.equivFunOnFinite.symm (occ x) = Finsupp.equivFunOnFinite.symm k
      then (1 : ℕ) else 0) = #{o : Fin n → α | occ o = k} := by
    rw [sum_boole]
    simp only [EmbeddingLike.apply_eq_iff_eq, Nat.cast_id]
  rw [hl] at hc
  rw [hc]
  have hr : ∀ x ∈ piAntidiag univ n, MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial univ x : MvPolynomial α ℕ) * ∏ i, MvPolynomial.X i ^ x i) =
      if x = k then Nat.multinomial univ k else 0 := by
    intro x _
    have hm : (∏ i, (MvPolynomial.X i : MvPolynomial α ℕ) ^ x i) =
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm x) 1 := by
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), map_one, one_mul]
      rfl
    rw [hm, ← map_natCast (MvPolynomial.C (σ := α) (R := ℕ)), MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_monomial]
    by_cases h : x = k
    · subst h; simp
    · have : Finsupp.equivFunOnFinite.symm x ≠ Finsupp.equivFunOnFinite.symm k := by
        simpa using h
      simp [this, h]
  rw [sum_congr rfl hr, sum_ite_eq' (piAntidiag univ n) k, if_pos hk]
theorem sum_occ {n : ℕ} {M : Type*} [AddCommMonoid M] (Ψ : (α → ℕ) → M) :
    ∑ o : Fin n → α, Ψ (occ o) = ∑ k ∈ piAntidiag univ n, Nat.multinomial univ k • Ψ k := by
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := piAntidiag univ n) (g := occ)
    (fun o _ => occ_mem_piAntidiag o)]
  refine sum_congr rfl fun k hk => ?_
  rw [sum_congr rfl (g := fun _ => Ψ k) (fun o ho => by rw [(mem_filter.mp ho).2]), sum_const,
    card_occ_eq k hk]
theorem prod_eq_prod_pow_occ {n : ℕ} {M : Type*} [CommMonoid M] (f : α → M) (o : Fin n → α) :
    ∏ i, f (o i) = ∏ a, f a ^ occ o a := by
  rw [← prod_fiberwise (s := univ) (g := o) (f := fun i => f (o i))]
  refine prod_congr rfl fun a _ => ?_
  rw [prod_congr rfl (g := fun _ => f a) (fun i hi => by rw [(mem_filter.mp hi).2]), prod_const]
  rfl
theorem sum_eq_sum_mul_occ {n : ℕ} (f : α → ℕ) (o : Fin n → α) :
    ∑ i, f (o i) = ∑ a, occ o a * f a := by
  rw [← sum_fiberwise (s := univ) (g := o) (f := fun i => f (o i))]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_congr rfl (g := fun _ => f a) (fun i hi => by rw [(mem_filter.mp hi).2]), sum_const,
    smul_eq_mul]
  rfl
end ClaudeWCT.Numerics
end
section
namespace ClaudeWCT.Numerics
open Finset
section IE
variable {c : ℕ} {β : Type*} [Fintype β]
def Violates (val : β → Fin c → ℕ) (v : Fin c → ℕ) (s : Fin c → Bool) (x : β) : Prop :=
  ∀ i, s i = true → val x i < v i
instance (val : β → Fin c → ℕ) (v : Fin c → ℕ) (s : Fin c → Bool) : DecidablePred (Violates val v s) :=
  fun _ => Fintype.decidableForallFintype
def CoversT {p : ℕ} (val : β → Fin c → ℕ) (v : Fin c → ℕ) (E : Fin p → β) : Prop :=
  ∀ i, ∃ j, v i ≤ val (E j) i
instance {p : ℕ} (val : β → Fin c → ℕ) (v : Fin c → ℕ) : DecidablePred (CoversT (p := p) val v) :=
  fun _ => Fintype.decidableForallFintype
omit [Fintype β] in
theorem indicator_covers {p : ℕ} (val : β → Fin c → ℕ) (v : Fin c → ℕ) (E : Fin p → β) :
    (if CoversT val v E then (1 : ℤ) else 0) =
      ∑ s : Fin c → Bool, (-1) ^ #{i | s i = true} *
        ∏ j, (if Violates val v s (E j) then (1 : ℤ) else 0) := by
  set a : Fin c → ℤ := fun i => ∏ j, (if val (E j) i < v i then (1 : ℤ) else 0) with ha
  have h1 : (if CoversT val v E then (1 : ℤ) else 0) = ∏ i, (1 - a i) := by
    by_cases h : CoversT val v E
    · rw [if_pos h]
      symm
      refine prod_eq_one fun i _ => ?_
      obtain ⟨j, hj⟩ := h i
      simp only [ha]
      rw [prod_eq_zero (mem_univ j) (by rw [if_neg (by omega)]), sub_zero]
    · rw [if_neg h]
      have h' : ∃ i, ∀ j, val (E j) i < v i := by
        by_contra hc
        push Not at hc
        exact h hc
      obtain ⟨i, hi⟩ := h'
      symm
      refine prod_eq_zero (mem_univ i) ?_
      rw [ha]
      simp only
      rw [prod_eq_one (fun j _ => by rw [if_pos (hi j)]), sub_self]
  rw [h1]
  have h2 : ∀ i, (1 - a i) = ∑ b : Bool, (if b = true then -a i else 1) := by
    intro i; rw [Fintype.sum_bool]; simp only [if_true]; simp; ring
  simp_rw [h2]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun s _ => ?_
  have h3 : ∀ i, (if s i = true then -a i else 1) = (if s i = true then (-1 : ℤ) else 1) *
      ∏ j, (if s i = true then (if val (E j) i < v i then (1 : ℤ) else 0) else 1) := by
    intro i
    by_cases hs : s i = true
    · simp [hs, ha]
    · simp [hs]
  rw [prod_congr rfl (fun i _ => h3 i), prod_mul_distrib]
  congr 1
  · rw [prod_ite, prod_const_one, mul_one, prod_const]
  · rw [prod_comm]
    refine prod_congr rfl fun j _ => ?_
    by_cases hv : Violates val v s (E j)
    · rw [if_pos hv]
      refine prod_eq_one fun i _ => ?_
      by_cases hs : s i = true
      · rw [if_pos hs, if_pos (hv i hs)]
      · rw [if_neg hs]
    · rw [if_neg hv]
      have hv' : ∃ i, s i = true ∧ ¬ val (E j) i < v i := by
        by_contra hc
        push Not at hc
        exact hv hc
      obtain ⟨i, hi1, hi2⟩ := hv'
      exact prod_eq_zero (mem_univ i) (by rw [if_pos hi1, if_neg hi2])
theorem card_covered_eq (p : ℕ) (val : β → Fin c → ℕ) (v : Fin c → ℕ) :
    (#{E : Fin p → β | CoversT val v E} : ℤ) =
      ∑ s : Fin c → Bool, (-1) ^ #{i | s i = true} * (#{x | Violates val v s x} : ℤ) ^ p := by
  rw [natCast_card_filter]
  simp_rw [indicator_covers]
  rw [sum_comm]
  refine sum_congr rfl fun s _ => ?_
  rw [← mul_sum, natCast_card_filter, Fintype.sum_pow]
end IE
section DP
open Polynomial
theorem card_pi_sum_eq_coeff {n : ℕ} {β : Type*} [DecidableEq β] (C : Fin n → Finset β) (g : β → ℕ)
    (t : ℕ) :
    #{x ∈ Fintype.piFinset C | ∑ i, g (x i) = t} =
      (∏ i, ∑ b ∈ C i, (X : ℕ[X]) ^ g b).coeff t := by
  rw [prod_univ_sum, finsetSum_coeff]
  simp_rw [prod_pow_eq_pow_sum, coeff_X_pow]
  rw [sum_boole, Nat.cast_id]
  congr 1
  ext x
  simp [eq_comm]
end DP
end ClaudeWCT.Numerics
end
section
namespace ClaudeWCT.Numerics.Kernel
open Finset
def parity (opts : List Opt) (k : Fin opts.length → ℕ) : Bool :=
  (∑ j, if (opts.get j).2.2.2 then k j else 0) % 2 == 1
theorem term_eq (hb total qIdx : ℕ) : ∀ (opts : List Opt) (k : Fin opts.length → ℕ) (rem q p fden : ℕ)
    (neg : Bool),
    term hb total qIdx opts k rem q p fden neg =
      if ∑ j, k j * (opts.get j).1 = rem then
        signedPair (neg ^^ parity opts k)
          ((fact total / (fden * ∏ j, (k j).factorial)) *
            coeffAt (q * ∏ j, (opts.get j).2.2.1 ^ k j) qIdx *
            hb ^ coeffAt (p * ∏ j, (opts.get j).2.1 ^ k j) 6)
      else 0
  | [], k, rem, q, p, fden, neg => by
    simp only [term, parity, List.length_nil, univ_eq_empty, sum_empty, prod_empty, mul_one,
      Nat.zero_mod]
    by_cases h : rem = 0
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]
  | (u, fu, fb, inS) :: os, k, rem, q, p, fden, neg => by
    rw [term, term_eq hb total qIdx os]
    have hS : ∑ j, k j * (((u, fu, fb, inS) :: os).get j).1 =
        k 0 * u + ∑ j, Fin.tail k j * (os.get j).1 :=
      Fin.sum_univ_succ (n := os.length) (fun j => k j * (((u, fu, fb, inS) :: os).get j).1)
    have hF : ∏ j, (k j).factorial = (k 0).factorial * ∏ j, (Fin.tail k j).factorial :=
      Fin.prod_univ_succ (n := os.length) (fun j => (k j).factorial)
    have hQ : ∏ j, (((u, fu, fb, inS) :: os).get j).2.2.1 ^ k j =
        fb ^ k 0 * ∏ j, (os.get j).2.2.1 ^ Fin.tail k j :=
      Fin.prod_univ_succ (n := os.length) (fun j => (((u, fu, fb, inS) :: os).get j).2.2.1 ^ k j)
    have hP : ∏ j, (((u, fu, fb, inS) :: os).get j).2.1 ^ k j =
        fu ^ k 0 * ∏ j, (os.get j).2.1 ^ Fin.tail k j :=
      Fin.prod_univ_succ (n := os.length) (fun j => (((u, fu, fb, inS) :: os).get j).2.1 ^ k j)
    have hpar : (neg ^^ parity ((u, fu, fb, inS) :: os) k) =
        ((neg ^^ (inS && k 0 % 2 == 1)) ^^ parity os (Fin.tail k)) := by
      have he : parity ((u, fu, fb, inS) :: os) k =
          (((if inS then k 0 else 0) + ∑ j, if (os.get j).2.2.2 then Fin.tail k j else 0) % 2 == 1) := by
        unfold parity
        exact congrArg (fun t => t % 2 == 1) (Fin.sum_univ_succ (n := os.length)
          (fun j => if (((u, fu, fb, inS) :: os).get j).2.2.2 then k j else 0))
      have he' : parity os (Fin.tail k) =
          ((∑ j, if (os.get j).2.2.2 then Fin.tail k j else 0) % 2 == 1) := rfl
      rw [he, he']
      generalize (∑ j, if (os.get j).2.2.2 then Fin.tail k j else 0) = S
      rcases Nat.mod_two_eq_zero_or_one (k 0) with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one S with h' | h' <;>
      cases inS <;> cases neg <;> simp [Nat.add_mod, h, h']
    rw [hS, hF, hQ, hP, hpar, ← mul_assoc fden, ← mul_assoc q, ← mul_assoc p]
    by_cases h1 : k 0 * u ≤ rem
    · rw [if_pos h1]
      by_cases h2 : ∑ j, Fin.tail k j * (os.get j).1 = rem - k 0 * u
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg h1, if_neg (by omega)]
end ClaudeWCT.Numerics.Kernel
end
section
namespace ClaudeWCT.Numerics.Kernel
theorem w1_ok : histEq (w1Hist HB) w1Data = true := by decide +kernel
theorem wf_ok : histEq (wfHist HB) wfData = true := by decide +kernel
theorem w2_ok : histEq (w2Hist HB) w2Data = true := by decide +kernel
theorem w1_mass : massOk (w1Hist 1) w1Data = true := by decide +kernel
theorem wf_mass : massOk (wfHist 1) wfData = true := by decide +kernel
theorem w2_mass : massOk (w2Hist 1) w2Data = true := by decide +kernel
end ClaudeWCT.Numerics.Kernel
end
section
namespace ClaudeWCT.Numerics.WCT9
open Finset Polynomial ClaudeWCT.Numerics ClaudeWCT.Numerics.Kernel
abbrev Word := {d : Fin 7 → Fin 4 // ∑ i, (d i : ℕ) = 6}
def wv (x : Word) : Fin 7 → ℕ := fun i => (x.1 i : ℕ)
def coverCount (p : ℕ) : ℕ := #{ue : Word × (Fin p → Word) | CoversT wv (wv ue.1) ue.2}
noncomputable def chainPoly (x : ℕ) (b : Bool) : ℕ[X] :=
  ∑ v ∈ univ.filter (fun v : Fin 4 => b = true → (v : ℕ) < x), X ^ (v : ℕ)
theorem card_word_filter (P : (Fin 7 → Fin 4) → Prop) [DecidablePred P] :
    #{x : Word | P x.1} = #{d : Fin 7 → Fin 4 | ∑ i, (d i : ℕ) = 6 ∧ P d} := by
  refine card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨x.2, hx⟩
  · intro x _ y _ h; exact Subtype.ext h
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    exact ⟨⟨d, hd.1⟩, by simp [hd.2], rfl⟩
theorem card_violates (u : Fin 7 → ℕ) (s : Fin 7 → Bool) :
    #{x : Word | Violates wv u s x} = (∏ i, chainPoly (u i) (s i)).coeff 6 := by
  have h1 : #{x : Word | Violates wv u s x} =
      #{d : Fin 7 → Fin 4 | ∑ i, (d i : ℕ) = 6 ∧ ∀ i, s i = true → (d i : ℕ) < u i} := by
    convert card_word_filter (fun d => ∀ i, s i = true → (d i : ℕ) < u i) using 3
    rfl
  rw [h1]
  unfold chainPoly
  have h2 := card_pi_sum_eq_coeff (fun i => univ.filter (fun v : Fin 4 => s i = true → (v : ℕ) < u i))
    (fun v : Fin 4 => (v : ℕ)) 6
  rw [← h2]
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  tauto
theorem coverCount_ie (p : ℕ) :
    (coverCount p : ℤ) = ∑ u : Word, ∑ s : Fin 7 → Bool,
      (-1) ^ #{i | s i = true} * (((∏ i, chainPoly (wv u i) (s i)).coeff 6 : ℕ) : ℤ) ^ p := by
  unfold coverCount
  rw [natCast_card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  dsimp only
  rw [← natCast_card_filter, card_covered_eq]
  simp_rw [card_violates]
def optOf (x : Fin 4) (b : Bool) : Fin 8 := ⟨2 * x.val + (if b then 1 else 0), by
  have := x.isLt; split <;> omega⟩
def ou (j : Fin 8) : Fin 4 := ⟨j.val / 2, by have := j.isLt; omega⟩
def osb (j : Fin 8) : Bool := decide (j.val % 2 = 1)
theorem ou_optOf (x : Fin 4) (b : Bool) : ou (optOf x b) = x := by
  ext; cases b <;> simp [ou, optOf]
  all_goals omega
theorem osb_optOf (x : Fin 4) (b : Bool) : osb (optOf x b) = b := by
  cases b <;> simp [osb, optOf]
theorem optOf_ou_osb (j : Fin 8) : optOf (ou j) (osb j) = j := by
  ext; simp only [optOf, ou, osb]
  by_cases h : j.val % 2 = 1 <;> simp [h] <;> omega
def optEquiv : (Fin 7 → Fin 4) × (Fin 7 → Bool) ≃ (Fin 7 → Fin 8) where
  toFun ds i := optOf (ds.1 i) (ds.2 i)
  invFun o := (fun i => ou (o i), fun i => osb (o i))
  left_inv ds := by ext i <;> simp [ou_optOf, osb_optOf]
  right_inv o := by ext i; simp [optOf_ou_osb]
noncomputable def cp (j : Fin 8) : ℕ[X] := chainPoly (ou j) (osb j)
noncomputable def psi1 (p : ℕ) (k : Fin 8 → ℕ) : ℤ :=
  if ∑ a, k a * ((ou a : ℕ)) = 6 then
    (-1) ^ (∑ a, k a * (if osb a then 1 else 0)) * (((∏ a, cp a ^ k a).coeff 6 : ℕ) : ℤ) ^ p
  else 0
theorem coverCount_occ (p : ℕ) :
    (coverCount p : ℤ) = ∑ o : Fin 7 → Fin 8, psi1 p (occ o) := by
  rw [coverCount_ie]
  have hsub : ∀ G : (Fin 7 → Fin 4) → ℤ, ∑ u : Word, G u.1 =
      ∑ d : Fin 7 → Fin 4, if ∑ i, (d i : ℕ) = 6 then G d else 0 := by
    intro G
    rw [← sum_filter, ← sum_subtype (p := fun d : Fin 7 → Fin 4 => ∑ i, (d i : ℕ) = 6)]
    intro d; simp
  simp only [wv]
  rw [hsub (fun d => ∑ s : Fin 7 → Bool, (-1) ^ #{i | s i = true} *
      (((∏ i, chainPoly ((d i : ℕ)) (s i)).coeff 6 : ℕ) : ℤ) ^ p)]
  simp_rw [ite_sum_zero]
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp optEquiv.symm]
  refine sum_congr rfl fun o _ => ?_
  have e1 : ∀ i, (optEquiv.symm o).1 i = ou (o i) := fun i => rfl
  have e2 : ∀ i, (optEquiv.symm o).2 i = osb (o i) := fun i => rfl
  simp only [e1, e2]
  unfold psi1
  have hsum : ∑ i, ((ou (o i) : Fin 4) : ℕ) = ∑ a, occ o a * (ou a : ℕ) :=
    sum_eq_sum_mul_occ (fun a => (ou a : ℕ)) o
  have hcard : #{i | osb (o i) = true} = ∑ a, occ o a * (if osb a then 1 else 0) := by
    rw [card_filter]
    exact sum_eq_sum_mul_occ (fun a => if osb a then 1 else 0) o
  have hprod : ∏ i, chainPoly ((ou (o i) : ℕ)) (osb (o i)) = ∏ a, cp a ^ occ o a :=
    prod_eq_prod_pow_occ cp o
  simp only [hsum, hcard, hprod]
theorem coverCount_counts (p : ℕ) :
    (coverCount p : ℤ) = ∑ k ∈ Nat.antidiagonalTuple 8 7, (Nat.multinomial univ k : ℤ) * psi1 p k := by
  rw [coverCount_occ, sum_occ, piAntidiag_univ_fin_eq_antidiagonalTuple]
  simp_rw [nsmul_eq_mul]
theorem optsU_fst (j : Fin 8) : (optsU.get j).1 = (ou j : ℕ) := by fin_cases j <;> rfl
theorem optsU_inS (j : Fin 8) : (optsU.get j).2.2.2 = osb j := by fin_cases j <;> rfl
theorem optsU_fb (j : Fin 8) : (optsU.get j).2.2.1 = 1 := by fin_cases j <;> rfl
theorem optsU_fu (j : Fin 8) : (optsU.get j).2.1 = (cp j).eval PB := by
  fin_cases j <;>
  simp [cp, chainPoly, ou, osb, Finset.sum_filter, Fin.sum_univ_four, optsU,
    chainFac, box, monos, List.range_succ] <;> decide
theorem eval_one_cp_le (j : Fin 8) : (cp j).eval 1 ≤ 4 := by
  unfold cp chainPoly
  rw [eval_finsetSum]
  simp only [eval_pow, eval_X, one_pow, sum_const, smul_eq_mul, mul_one]
  exact (card_filter_le _ _).trans (by simp)
theorem coeff_prod_cp_lt (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 7) (i : ℕ) :
    (∏ a, cp a ^ k a).coeff i < PB := by
  refine lt_of_le_of_lt (coeff_le_eval_one _ i) ?_
  rw [eval_prod]
  simp only [eval_pow]
  have hsum : ∑ a, k a = 7 := Nat.mem_antidiagonalTuple.mp hk
  calc ∏ a, (cp a).eval 1 ^ k a ≤ ∏ a, 4 ^ k a :=
        prod_le_prod' fun a _ => Nat.pow_le_pow_left (eval_one_cp_le a) _
    _ = 4 ^ 7 := by rw [prod_pow_eq_pow_sum, hsum]
    _ < PB := by unfold PB; norm_num
theorem w1Hist_eq (hb : ℕ) :
    w1Hist hb = histOf (Nat.antidiagonalTuple 8 7) (fun k => ∑ j, k j * (ou j : ℕ) = 6)
      (fun k => parity optsU k) (fun k => Nat.multinomial univ k)
      (fun k => coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6) hb := by
  unfold w1Hist histOf
  have h1 : enumK hb 7 0 optsU 7 6 1 1 1 false =
      ∑ k ∈ Nat.antidiagonalTuple 8 7, term hb 7 0 optsU k 6 1 1 1 false :=
    enumK_eq hb 7 0 optsU 7 6 1 1 1 false
  rw [h1]
  refine sum_congr rfl fun k hk => ?_
  have hsum : ∑ a, k a = 7 := Nat.mem_antidiagonalTuple.mp hk
  have h2 : term hb 7 0 optsU k 6 1 1 1 false =
      if ∑ j : Fin 8, k j * (optsU.get j).1 = 6 then
        signedPair (false ^^ parity optsU k)
          ((fact 7 / (1 * ∏ j : Fin 8, (k j).factorial)) *
            coeffAt (1 * ∏ j : Fin 8, (optsU.get j).2.2.1 ^ k j) 0 *
            hb ^ coeffAt (1 * ∏ j : Fin 8, (optsU.get j).2.1 ^ k j) 6)
      else 0 :=
    term_eq hb 7 0 optsU k 6 1 1 1 false
  rw [h2]
  simp only [optsU_fst, optsU_fb, optsU_fu, one_pow, prod_const_one, one_mul, Bool.false_xor]
  have hm : fact 7 / ∏ j, (k j).factorial = Nat.multinomial univ k := by
    rw [fact_eq, Nat.multinomial, ← hsum]
  have hc : coeffAt 1 0 = 1 := by unfold coeffAt PB; norm_num
  rw [hm, hc, mul_one]
theorem neg_one_pow_eq (n : ℕ) : (-1 : ℤ) ^ n = if n % 2 == 1 then -1 else 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, if_neg]; rw [Nat.even_iff] at h; simp [h]
  · rw [h.neg_one_pow, if_pos]; rw [Nat.odd_iff] at h; simp [h]
theorem term_match (p : ℕ) (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 7) :
    (Nat.multinomial univ k : ℤ) * psi1 p k =
      if ∑ j, k j * (ou j : ℕ) = 6 then
        (if parity optsU k then (-1 : ℤ) else 1) * (Nat.multinomial univ k : ℕ) *
          ((coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6 : ℕ) : ℤ) ^ p
      else 0 := by
  unfold psi1
  have hpar : parity optsU k = ((∑ a, k a * (if osb a then 1 else 0)) % 2 == 1) := by
    have h0 : parity optsU k = ((∑ j : Fin 8, if (optsU.get j).2.2.2 then k j else 0) % 2 == 1) := rfl
    rw [h0]
    congr 2
    refine sum_congr rfl fun j _ => ?_
    rw [optsU_inS]; split <;> simp
  have hcnt : coeffAt (∏ j, ((cp j).eval PB) ^ k j) 6 = (∏ a, cp a ^ k a).coeff 6 := by
    have he : ∏ j, ((cp j).eval PB) ^ k j = (∏ a, cp a ^ k a).eval PB := by
      rw [eval_prod]; simp only [eval_pow]
    rw [he]
    exact eval_div_pow_mod (by unfold PB; positivity) 6 _ (coeff_prod_cp_lt k hk)
  rw [hpar, hcnt, ← neg_one_pow_eq]
  split
  · ring
  · simp
theorem coverCount_eq (p : ℕ) :
    (coverCount p : ℤ) = (w1Data.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  have hEq := w1_ok
  have hMass := w1_mass
  rw [w1Hist_eq] at hEq hMass
  rw [coverCount_counts, ← decode _ _ _ _ _ w1Data hEq hMass p]
  exact sum_congr rfl fun k hk => term_match p k hk
end ClaudeWCT.Numerics.WCT9
end
end
-- ==== merged from ClaudeWCT_Numerics_CoverWF ====
section

namespace ClaudeWCT.Numerics
open Finset
section
variable {c : ℕ} {β : Type*}
def CoversExcept {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (v : Fin c → ℕ) (E : Fin p → β) :
    Prop :=
  ∀ j, j ≠ i → ∃ e, v j ≤ val (E e) j
instance {p : ℕ} (val : β → Fin c → ℕ) (i : Fin c) (v : Fin c → ℕ) :
    DecidablePred (CoversExcept (p := p) val i v) :=
  fun _ => Fintype.decidableForallFintype
theorem coversExcept_iff {p : ℕ} (val : β → Fin (c + 1) → ℕ) (i : Fin (c + 1))
    (v : Fin (c + 1) → ℕ) (E : Fin p → β) :
    CoversExcept val i v E ↔
      CoversT (fun x j => val x (i.succAbove j)) (fun j => v (i.succAbove j)) E := by
  constructor
  · intro h j
    exact h _ (Fin.succAbove_ne i j)
  · intro h j hj
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact h j'
end
end ClaudeWCT.Numerics
namespace ClaudeWCT.Numerics.WCT9
open Finset Polynomial ClaudeWCT.Numerics ClaudeWCT.Numerics.Kernel
def coverCountF (i : Fin 7) (p : ℕ) : ℕ :=
  #{ue : Word × (Fin p → Word) | CoversExcept wv i (wv ue.1) ue.2}
theorem chainPoly_false (x : ℕ) : chainPoly x false = cp 0 := by
  have h0 : osb 0 = false := rfl
  simp [cp, chainPoly, h0]
theorem box_three_eq : box 3 = (cp 0).eval PB := optsU_fu 0
theorem card_violates_off (i : Fin 7) (u : Fin 7 → ℕ) (s : Fin 6 → Bool) :
    #{x : Word | Violates (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) s x} =
      (cp 0 * ∏ j, chainPoly (u (i.succAbove j)) (s j)).coeff 6 := by
  have h1 : #{x : Word | Violates (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) s x} =
      #{x : Word | Violates wv u (Fin.insertNth (α := fun _ => Bool) i false s) x} := by
    refine congrArg card (filter_congr fun x _ => ?_)
    simp only [Violates]
    rw [Fin.forall_iff_succAbove i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Bool.false_eq_true,
      false_implies, true_and]
  rw [h1, card_violates, Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, chainPoly_false]
theorem card_coversExcept (i : Fin 7) (p : ℕ) (u : Fin 7 → ℕ) :
    (#{E : Fin p → Word | CoversExcept wv i u E} : ℤ) =
      ∑ s : Fin 6 → Bool, (-1) ^ #{j | s j = true} *
        (((cp 0 * ∏ j, chainPoly (u (i.succAbove j)) (s j)).coeff 6 : ℕ) : ℤ) ^ p := by
  have h : #{E : Fin p → Word | CoversExcept wv i u E} =
      #{E : Fin p → Word | CoversT (fun x j => wv x (i.succAbove j)) (fun j => u (i.succAbove j)) E} :=
    congrArg card (filter_congr fun E _ => coversExcept_iff _ _ _ _)
  rw [h, card_covered_eq]
  simp_rw [card_violates_off]
theorem coverCountF_ie (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ u : Word, ∑ s : Fin 6 → Bool,
      (-1) ^ #{j | s j = true} *
        (((cp 0 * ∏ j, chainPoly (wv u (i.succAbove j)) (s j)).coeff 6 : ℕ) : ℤ) ^ p := by
  unfold coverCountF
  rw [natCast_card_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun u _ => ?_
  dsimp only
  rw [← natCast_card_filter, card_coversExcept]
def optEquivN (n : ℕ) : (Fin n → Fin 4) × (Fin n → Bool) ≃ (Fin n → Fin 8) where
  toFun ds i := optOf (ds.1 i) (ds.2 i)
  invFun o := (fun i => ou (o i), fun i => osb (o i))
  left_inv ds := by ext i <;> simp [ou_optOf, osb_optOf]
  right_inv o := by ext i; simp [optOf_ou_osb]
noncomputable def psiF (p : ℕ) (x : ℕ) (k : Fin 8 → ℕ) : ℤ :=
  if x + ∑ a, k a * ((ou a : ℕ)) = 6 then
    (-1) ^ (∑ a, k a * (if osb a then 1 else 0)) *
      (((cp 0 * ∏ a, cp a ^ k a).coeff 6 : ℕ) : ℤ) ^ p
  else 0
theorem coverCountF_occ (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ x : Fin 4, ∑ o : Fin 6 → Fin 8, psiF p x (occ o) := by
  rw [coverCountF_ie]
  have hsub : ∀ G : (Fin 7 → Fin 4) → ℤ, ∑ u : Word, G u.1 =
      ∑ d : Fin 7 → Fin 4, if ∑ i, (d i : ℕ) = 6 then G d else 0 := by
    intro G
    rw [← sum_filter, ← sum_subtype (p := fun d : Fin 7 → Fin 4 => ∑ i, (d i : ℕ) = 6)]
    intro d; simp
  simp only [wv]
  rw [hsub (fun d => ∑ s : Fin 6 → Bool, (-1) ^ #{j | s j = true} *
      (((cp 0 * ∏ j, chainPoly ((d (i.succAbove j) : ℕ)) (s j)).coeff 6 : ℕ) : ℤ) ^ p)]
  rw [← Equiv.sum_comp (Fin.insertNthEquiv (fun _ => Fin 4) i), Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  have hins : ∀ d' : Fin 6 → Fin 4, (Fin.insertNthEquiv (fun _ => Fin 4) i) (x, d') =
      Fin.insertNth (α := fun _ => Fin 4) i x d' := fun _ => rfl
  simp only [hins, Fin.insertNth_apply_succAbove]
  have hsplit : ∀ d' : Fin 6 → Fin 4,
      ∑ j, ((Fin.insertNth (α := fun _ => Fin 4) i x d' j : Fin 4) : ℕ) = (x : ℕ) + ∑ j, (d' j : ℕ) := by
    intro d'
    rw [Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [hsplit]
  simp_rw [ite_sum_zero]
  rw [← Fintype.sum_prod_type']
  rw [← Equiv.sum_comp (optEquivN 6).symm]
  refine sum_congr rfl fun o _ => ?_
  have e1 : ∀ j, ((optEquivN 6).symm o).1 j = ou (o j) := fun j => rfl
  have e2 : ∀ j, ((optEquivN 6).symm o).2 j = osb (o j) := fun j => rfl
  simp only [e1, e2]
  unfold psiF
  have hsum : ∑ j, ((ou (o j) : Fin 4) : ℕ) = ∑ a, occ o a * (ou a : ℕ) :=
    sum_eq_sum_mul_occ (fun a => (ou a : ℕ)) o
  have hcard : #{j | osb (o j) = true} = ∑ a, occ o a * (if osb a then 1 else 0) := by
    rw [card_filter]
    exact sum_eq_sum_mul_occ (fun a => if osb a then 1 else 0) o
  have hprod : ∏ j, chainPoly ((ou (o j) : ℕ)) (osb (o j)) = ∏ a, cp a ^ occ o a :=
    prod_eq_prod_pow_occ cp o
  simp only [hsum, hcard, hprod]
theorem coverCountF_counts (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = ∑ x : Fin 4,
      ∑ k ∈ Nat.antidiagonalTuple 8 6, (Nat.multinomial univ k : ℤ) * psiF p x k := by
  rw [coverCountF_occ]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_occ, piAntidiag_univ_fin_eq_antidiagonalTuple]
  simp_rw [nsmul_eq_mul]
theorem coeff_free_prod_cp_lt (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 6) (n : ℕ) :
    (cp 0 * ∏ a, cp a ^ k a).coeff n < PB := by
  refine lt_of_le_of_lt (coeff_le_eval_one _ n) ?_
  rw [eval_mul, eval_prod]
  simp only [eval_pow]
  have hsum : ∑ a, k a = 6 := Nat.mem_antidiagonalTuple.mp hk
  calc (cp 0).eval 1 * ∏ a, (cp a).eval 1 ^ k a ≤ 4 * ∏ a, 4 ^ k a :=
        Nat.mul_le_mul (eval_one_cp_le 0)
          (prod_le_prod' fun a _ => Nat.pow_le_pow_left (eval_one_cp_le a) _)
    _ = 4 * 4 ^ 6 := by rw [prod_pow_eq_pow_sum, hsum]
    _ < PB := by unfold PB; norm_num
theorem wfHist_sum (hb : ℕ) :
    wfHist hb = ∑ x : Fin 4, enumK hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  have c0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  have c1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have c2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have c3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  rw [Fin.sum_univ_four]
  simp only [wfHist, hr, List.foldr_cons, List.foldr_nil]
  ext <;> simp only [Prod.fst_add, Prod.snd_add, c0, c1, c2, c3, add_zero, add_assoc]
theorem wfHist_eq (hb : ℕ) :
    wfHist hb = histOf ((univ : Finset (Fin 4)) ×ˢ Nat.antidiagonalTuple 8 6)
      (fun xk => ∑ j, xk.2 j * (ou j : ℕ) = 6 - (xk.1 : ℕ))
      (fun xk => parity optsU xk.2) (fun xk => Nat.multinomial univ xk.2)
      (fun xk => coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ xk.2 j) 6) hb := by
  rw [wfHist_sum]
  unfold histOf
  rw [sum_product]
  refine sum_congr rfl fun x _ => ?_
  have h1 : enumK hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false =
      ∑ k ∈ Nat.antidiagonalTuple 8 6, term hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false :=
    enumK_eq hb 6 0 optsU 6 (6 - (x : ℕ)) 1 (box 3) 1 false
  rw [h1]
  refine sum_congr rfl fun k hk => ?_
  have hsum : ∑ a, k a = 6 := Nat.mem_antidiagonalTuple.mp hk
  have h2 : term hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false =
      if ∑ j : Fin 8, k j * (optsU.get j).1 = 6 - (x : ℕ) then
        signedPair (false ^^ parity optsU k)
          ((fact 6 / (1 * ∏ j : Fin 8, (k j).factorial)) *
            coeffAt (1 * ∏ j : Fin 8, (optsU.get j).2.2.1 ^ k j) 0 *
            hb ^ coeffAt (box 3 * ∏ j : Fin 8, (optsU.get j).2.1 ^ k j) 6)
      else 0 :=
    term_eq hb 6 0 optsU k (6 - (x : ℕ)) 1 (box 3) 1 false
  rw [h2]
  simp only [optsU_fst, optsU_fb, optsU_fu, one_pow, prod_const_one, one_mul, Bool.false_xor]
  have hm : fact 6 / ∏ j, (k j).factorial = Nat.multinomial univ k := by
    rw [fact_eq, Nat.multinomial, ← hsum]
  have hc : coeffAt 1 0 = 1 := by unfold coeffAt PB; norm_num
  rw [hm, hc, mul_one]
theorem term_matchF (p : ℕ) (x : Fin 4) (k : Fin 8 → ℕ) (hk : k ∈ Nat.antidiagonalTuple 8 6) :
    (Nat.multinomial univ k : ℤ) * psiF p x k =
      if ∑ j, k j * (ou j : ℕ) = 6 - (x : ℕ) then
        (if parity optsU k then (-1 : ℤ) else 1) * (Nat.multinomial univ k : ℕ) *
          ((coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ k j) 6 : ℕ) : ℤ) ^ p
      else 0 := by
  unfold psiF
  have hpar : parity optsU k = ((∑ a, k a * (if osb a then 1 else 0)) % 2 == 1) := by
    have h0 : parity optsU k = ((∑ j : Fin 8, if (optsU.get j).2.2.2 then k j else 0) % 2 == 1) := rfl
    rw [h0]
    congr 2
    refine sum_congr rfl fun j _ => ?_
    rw [optsU_inS]; split <;> simp
  have hcnt : coeffAt (box 3 * ∏ j, ((cp j).eval PB) ^ k j) 6 = (cp 0 * ∏ a, cp a ^ k a).coeff 6 := by
    have he : box 3 * ∏ j, ((cp j).eval PB) ^ k j = (cp 0 * ∏ a, cp a ^ k a).eval PB := by
      rw [eval_mul, eval_prod, box_three_eq]; simp only [eval_pow]
    rw [he]
    exact eval_div_pow_mod (by unfold PB; positivity) 6 _ (coeff_free_prod_cp_lt k hk)
  rw [hpar, hcnt, ← neg_one_pow_eq]
  have hx : (x : ℕ) < 4 := x.isLt
  by_cases h : ∑ j, k j * (ou j : ℕ) = 6 - (x : ℕ)
  · rw [if_pos (by omega), if_pos h]
    ring
  · rw [if_neg (by omega), if_neg h, mul_zero]
theorem coverCountF_eq (i : Fin 7) (p : ℕ) :
    (coverCountF i p : ℤ) = (wfData.map (fun e => e.2 * (e.1 : ℤ) ^ p)).sum := by
  have hEq := wf_ok
  have hMass := wf_mass
  rw [wfHist_eq] at hEq hMass
  rw [coverCountF_counts, ← decode _ _ _ _ _ wfData hEq hMass p, sum_product]
  exact sum_congr rfl fun x _ => sum_congr rfl fun k hk => term_matchF p x k hk
end ClaudeWCT.Numerics.WCT9
end
