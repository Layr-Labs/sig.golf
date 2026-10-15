import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import SigGolfCandidate.ClaudeWCT.Numerics.LowerCreditCount
import SigGolfCandidate.ClaudeWCT.Numerics.LowerZeroCreditPoly

namespace ClaudeWCT.Numerics.LowerZeroCredit
open Finset
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
set_option Elab.async false

/-- Packed payload statistics; the checksum is tested explicitly below. -/
def accZ (T f E : ℕ) : Bool := decide (
  E / 64 % 512 ≤ T ∧ T - E / 64 % 512 < 8 ∧
  f ≤ E % 64 + (if T - E / 64 % 512 = 6 then 1 else 0) ∧
  E / 32768 + (if T - E / 64 % 512 = 0 then 1 else 0) ≤ 5)
def winZ (T z : ℕ) : Finset ℕ :=
  Ico (32768*z+64*(T-7)) (32768*z+64*(T-7)+512)
def windowsZ (T : ℕ) : Finset ℕ := (range 6).biUnion (winZ T)

theorem accZ_window {T f E : ℕ} (hT : 7 ≤ T ∧ T < 512)
    (h : accZ T f E = true) : E ∈ windowsZ T := by
  simp only [accZ, decide_eq_true_eq] at h
  have hr : E % 32768 / 64 = E / 64 % 512 := Nat.mod_mul_left_div_self E 64 512
  unfold windowsZ
  apply mem_biUnion.mpr
  refine ⟨E/32768, mem_range.mpr (by split_ifs at h <;> omega), ?_⟩
  simp only [winZ, mem_Ico]
  constructor <;> omega

theorem windowsZ_disjoint {T : ℕ} (hT : 7 ≤ T ∧ T < 512) :
    Set.PairwiseDisjoint (↑(range 6)) (winZ T) := by
  intro z hz z' hz' hne
  apply disjoint_left.mpr
  intro E hE hE'
  simp only [winZ, mem_Ico] at hE hE'
  omega

/-- Seven nonzero digit monomials: no high-degree zero-marker evaluation. -/
def nonzeroEvalZ (B : ℕ) : ℕ := B^64+B^128+B^192+B^256+B^320+B^385+B^448
/-- Binomial zero-count coefficient, with one shift/truncation outside each fold. -/
def windowCountZ (T f z : ℕ) : ℕ :=
  let start := 64*(T-7)
  let window := nonzeroEvalZ (2^128)^(42-z) / (2^128)^start % (2^128)^512
  (List.range 512).foldr (fun j a =>
    (if accZ T f (32768*z+start+j) = true then
      Nat.choose 42 z * (window / (2^128)^j % 2^128) else 0) + a) 0
def countCheckZ (T f count : ℕ) : Bool :=
  Nat.beq ((List.range 6).foldr (fun z a => windowCountZ T f z + a) 0) count

theorem window_digitZ (n B A j k : ℕ) (hj : j < k) :
    (n / B^A % B^k) / B^j % B = n / B^(A+j) % B := by
  have hp : B^k = B^j * B^(k-j) := by rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hj)]
  rw [hp, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (by
    exact dvd_pow_self B (Nat.sub_pos_of_lt hj).ne')]
  rw [Nat.div_div_eq_div_mul, ← pow_add]

#time theorem check_199_4 : countCheckZ 199 4 90649243438620156062228389214105950 = true := by decide +kernel
#time theorem check_199_5 : countCheckZ 199 5 87421058181341847220388848563308770 = true := by decide +kernel
#time theorem check_200_4 : countCheckZ 200 4 72459682149134130685732695915636483 = true := by decide +kernel
end ClaudeWCT.Numerics.LowerZeroCredit

namespace ClaudeWCT.Numerics.LowerZeroCredit
open Finset Polynomial
open ClaudeWCT.Numerics.LowerCredit
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-- Packed statistics: credit<64, sum<512, zeros<64. -/
def wtZ (a : ℕ) : ℕ := 64 * a + (if a = 6 then 1 else 0) + 32768 * (if a = 0 then 1 else 0)
def LowerAcceptZ (T f n : ℕ) : Prop := LowerAccept T f n ∧
  (lowerDigits n ++ [T - (lowerDigits n).sum]).count 0 ≤ 5
instance (T f n : ℕ) : Decidable (LowerAcceptZ T f n) := by unfold LowerAcceptZ; infer_instance

theorem sum_map_wtZ (l : List ℕ) :
    (l.map wtZ).sum = 32768 * l.count 0 + 64 * l.sum + l.count 6 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.count_cons, List.count_cons]
      unfold wtZ
      by_cases h0 : a = 0
      · subst a; simp; omega
      · by_cases h6 : a = 6
        · subst a; simp; omega
        · simp [h0, h6]; omega

def statZ (d : Fin 42 → Fin 8) : ℕ := ∑ i, wtZ (d i)
theorem statZ_eq (d : Fin 42 → Fin 8) :
    statZ d = 32768 * (lowerDigits (finFunctionFinEquiv d)).count 0 +
      64 * (lowerDigits (finFunctionFinEquiv d)).sum + (lowerDigits (finFunctionFinEquiv d)).count 6 := by
  rw [← sum_map_wtZ, lowerDigits_equiv, List.map_ofFn, List.sum_ofFn]
  rfl


theorem accept_list_iffZ (T f : ℕ) (L : List ℕ) (hlen : L.length = 42)
    (hsum : L.sum < 512) (E : ℕ)
    (hE : E = 32768 * L.count 0 + 64 * L.sum + L.count 6) :
    (L.sum ≤ T ∧ T - L.sum < 8 ∧ f ≤ (L ++ [T - L.sum]).count 6 ∧
      (L ++ [T - L.sum]).count 0 ≤ 5) ↔ accZ T f E = true := by
  have hc6 : L.count 6 ≤ 42 := hlen ▸ List.count_le_length ..
  have hc0 : L.count 0 ≤ 42 := hlen ▸ List.count_le_length ..
  have e1 : E % 64 = L.count 6 := by omega
  have e2 : E / 64 % 512 = L.sum := by omega
  have e3 : E / 32768 = L.count 0 := by omega
  have hcount (a : ℕ) : (L ++ [T - L.sum]).count a = L.count a + if T - L.sum = a then 1 else 0 := by
    rw [List.count_append]
    by_cases h : T - L.sum = a <;> simp [h]
  simp only [accZ, decide_eq_true_iff, e1, e2, e3, hcount]

theorem list_sum_bound (l : List ℕ) (h : ∀ a ∈ l, a ≤ 7) : l.sum ≤ 7 * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := h a (by simp)
      have hl := ih (fun b hb => h b (by simp [hb]))
      simp only [List.sum_cons, List.length_cons]
      omega

theorem accept_iffZ (T f : ℕ) (d : Fin 42 → Fin 8) :
    LowerAcceptZ T f (finFunctionFinEquiv d) ↔ accZ T f (statZ d) = true := by
  let L := lowerDigits (finFunctionFinEquiv d)
  have hlen : L.length = 42 := by
    dsimp only [L]
    rw [lowerDigits_equiv, List.length_ofFn]
  have hs : L.sum < 512 := by
    have hsum := list_sum_bound L (fun a ha => by
      dsimp only [L] at ha
      rw [lowerDigits_equiv] at ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      have := (d i).isLt
      omega)
    rw [hlen] at hsum
    omega
  have hacc := accept_list_iffZ T f _ hlen hs _ (statZ_eq d)
  unfold LowerAcceptZ LowerAccept
  constructor
  · intro h
    exact hacc.mp ⟨h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2⟩
  · intro h
    obtain ⟨hsum, hcs, hcredit, hzero⟩ := hacc.mpr h
    exact ⟨⟨equiv_lt d, hsum, hcs, hcredit⟩, hzero⟩


def baseEvalZ (B : ℕ) : ℕ :=
  B ^ wtZ 0 + B ^ wtZ 1 + B ^ wtZ 2 + B ^ wtZ 3 + B ^ wtZ 4 + B ^ wtZ 5 + B ^ wtZ 6 + B ^ wtZ 7
export LowerZeroCreditPoly (basePolyZ nonzeroPolyZ basePolyZ_split nonzeroPolyZ_degree coeff_splitZ)

theorem card_statZ_eq (E : ℕ) : #{d : Fin 42 → Fin 8 | statZ d = E} = (basePolyZ ^ 42).coeff E := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (fun _ : Fin 42 => (univ : Finset (Fin 8)))
    (fun b : Fin 8 => wtZ b) E
  rw [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at h
  exact h

theorem eval_basePolyZ (B : ℕ) : basePolyZ.eval B = baseEvalZ B := by
  simp [basePolyZ, LowerZeroCreditPoly.basePolyZ, Fin.sum_univ_eight,
    baseEvalZ, wtZ, LowerZeroCreditPoly.wtZ]
theorem coeff_ltZ (i : ℕ) : (basePolyZ ^ 42).coeff i < 2 ^ 128 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
  rw [eval_pow, eval_basePolyZ]
  norm_num [baseEvalZ]
theorem eval_nonzeroPolyZ (B : ℕ) : nonzeroPolyZ.eval B = nonzeroEvalZ B :=
  LowerZeroCreditPoly.eval_nonzeroPolyZ B

theorem coeff_nonzero_ltZ {k : ℕ} (hk : k ≤ 42) (i : ℕ) :
    (nonzeroPolyZ^k).coeff i < 2^128 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
  rw [eval_pow, eval_nonzeroPolyZ]
  norm_num [nonzeroEvalZ]
  exact (Nat.pow_le_pow_right (by decide : 0 < 7) hk).trans_lt (by norm_num)

theorem coeff_nonzero_eqZ {k : ℕ} (hk : k ≤ 42) (E : ℕ) :
    (nonzeroPolyZ^k).coeff E = nonzeroEvalZ (2^128)^k / (2^128)^E % 2^128 := by
  rw [← ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) E _ (coeff_nonzero_ltZ hk),
    eval_pow, eval_nonzeroPolyZ]


theorem windowCountZ_eq_sum {T : ℕ} (hT : 7 ≤ T ∧ T < 512) (f z : ℕ) (hz : z < 6) :
    windowCountZ T f z = ∑ j ∈ range 512,
      if accZ T f (32768*z+64*(T-7)+j) = true then
        (basePolyZ^42).coeff (32768*z+64*(T-7)+j) else 0 := by
  unfold windowCountZ
  rw [range_foldr_eq_sum]
  apply sum_congr rfl
  intro j hj
  have hj' : j < 512 := mem_range.mp hj
  have hR : 64*(T-7)+j < 32768 := by omega
  split_ifs
  · rw [window_digitZ _ _ _ _ _ hj']
    rw [show 32768*z+64*(T-7)+j = 32768*z+(64*(T-7)+j) by omega,
      coeff_splitZ (by omega) hR, coeff_nonzero_eqZ (by omega)]
  · rfl

theorem card_bitVec_eqZ (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptZ T f v.toNat).card =
      #{d : Fin 42 → Fin 8 | accZ T f (statZ d) = true} := by
  refine Finset.card_nbij' (fun v => finFunctionFinEquiv.symm ⟨v.toNat % 8 ^ 42, Nat.mod_lt _ (by positivity)⟩)
    (fun d => BitVec.ofNat 128 (finFunctionFinEquiv d)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1.1 (by norm_num))
    rw [← accept_iffZ, Equiv.apply_symm_apply]
    simpa only [hv'] using hv
  · intro d hd
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num))]
    exact (accept_iffZ T f d).mpr hd
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1.1 (by norm_num))
    simp only [Equiv.apply_symm_apply, hv']
    exact BitVec.ofNat_toNat ..
  · intro d _
    simp only
    apply finFunctionFinEquiv.symm_apply_eq.mpr
    apply Fin.ext
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num)), Nat.mod_eq_of_lt (finFunctionFinEquiv d).isLt]

theorem card_lowerAcceptZ_of_check (T f count : ℕ) (hT : 7 ≤ T ∧ T < 512)
    (hcheck : countCheckZ T f count = true) :
    (univ.filter fun v : BitVec 128 => LowerAcceptZ T f v.toNat).card = count := by
  rw [card_bitVec_eqZ, card_eq_sum_card_fiberwise (f := statZ) (t := windowsZ T)
    (fun d hd => accZ_window hT (by simpa using hd))]
  have hfib : ∀ E ∈ windowsZ T,
      #{d ∈ {d : Fin 42 → Fin 8 | accZ T f (statZ d) = true} | statZ d = E} =
        if accZ T f E = true then (basePolyZ^42).coeff E else 0 := by
    intro E _
    rw [filter_filter, ← card_statZ_eq]
    split_ifs with hE
    · exact congrArg Finset.card (filter_congr fun d _ => ⟨fun h => h.2, fun h => ⟨h ▸ hE, h⟩⟩)
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro d _ h
      exact hE (h.2 ▸ h.1)
  rw [sum_congr rfl hfib]
  have hsum : (∑ E ∈ windowsZ T, if accZ T f E = true then (basePolyZ^42).coeff E else 0) =
      (List.range 6).foldr (fun z a => windowCountZ T f z + a) 0 := by
    unfold windowsZ
    rw [sum_biUnion (windowsZ_disjoint hT), range_foldr_eq_sum]
    apply sum_congr rfl
    intro z hz
    rw [windowCountZ_eq_sum hT f z (mem_range.mp hz)]
    unfold winZ
    rw [sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  rw [hsum]
  exact Nat.eq_of_beq_eq_true hcheck

def LowerAcceptS1Z (T f n : ℕ) : Prop := LowerAcceptS1 T f n ∧
  (lowerDigitsS1 n ++ [T - (lowerDigitsS1 n).sum]).count 0 ≤ 5
instance (T f n : ℕ) : Decidable (LowerAcceptS1Z T f n) := by unfold LowerAcceptS1Z; infer_instance

theorem lowerAcceptS1Z_iff {m : ℕ} (hm : m < 2 ^ 128) (hs : SpareS1 m) (T f : ℕ) :
    LowerAcceptS1Z T f m ↔ LowerAcceptZ T f (ofS1 m) := by
  unfold LowerAcceptS1Z LowerAcceptZ
  rw [lowerAcceptS1_iff hm hs, lowerDigitsS1_eq hm hs]
theorem lowerAcceptS1Z_toS1 {n : ℕ} (T f : ℕ) (h : LowerAcceptZ T f n) : LowerAcceptS1Z T f (toS1 n) := by
  exact ⟨lowerAcceptS1_toS1 T f h.1, by simpa only [lowerDigitsS1_toS1] using h.2⟩
theorem card_lowerAcceptS1Z (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Z T f v.toNat).card =
      (univ.filter fun v : BitVec 128 => LowerAcceptZ T f v.toNat).card := by
  refine Finset.card_nbij' (fun v => BitVec.ofNat 128 (ofS1 v.toNat)) (fun v => BitVec.ofNat 128 (toS1 v.toNat))
    ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num))]
    exact (lowerAcceptS1Z_iff v.isLt hv.1.2.1 T f).mp hv
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toS1_lt hv.1.1)]
    exact lowerAcceptS1Z_toS1 T f hv
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num)),
      Nat.mod_eq_of_lt (toS1_lt (ofS1_lt _)), toS1_ofS1 v.isLt hv.1.2.1]
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toS1_lt hv.1.1),
      Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num)), ofS1_toS1 hv.1.1]

/-- Exact kernel-checked owner counts are imported from LowerZeroCreditWindow. -/

theorem card_lowerAcceptS1Z_199_4 :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Z 199 4 v.toNat).card = 90649243438620156062228389214105950 := by
  rw [card_lowerAcceptS1Z]; exact card_lowerAcceptZ_of_check _ _ _ (by decide) check_199_4
theorem card_lowerAcceptS1Z_199_5 :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Z 199 5 v.toNat).card = 87421058181341847220388848563308770 := by
  rw [card_lowerAcceptS1Z]; exact card_lowerAcceptZ_of_check _ _ _ (by decide) check_199_5
theorem card_lowerAcceptS1Z_200_4 :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Z 200 4 v.toNat).card = 72459682149134130685732695915636483 := by
  rw [card_lowerAcceptS1Z]; exact card_lowerAcceptZ_of_check _ _ _ (by decide) check_200_4
end ClaudeWCT.Numerics.LowerZeroCredit

section
namespace ClaudeWCT.Numerics.LowerRank
open Finset Polynomial LowerCredit LowerZeroCredit
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option Elab.async false

def rankFloor (i : ℕ) : ℕ := if i = 1 ∨ i = 8 then 5 else 3

def slot (i : Fin 14) (j : Fin 3) : Fin 42 := ⟨3 * i.val + j.val, by omega⟩
def special (i : Fin 14) (j : Fin 42) : Prop := j = slot i 0 ∨ j = slot i 1 ∨ j = slot i 2
instance (i : Fin 14) (j : Fin 42) : Decidable (special i j) := by unfold special; infer_instance
def allowed (i : Fin 14) (j : Fin 42) : Finset (Fin 8) :=
  if j = slot i 0 then univ.filter (fun a => a.val < rankFloor i.val)
  else if j = slot i 1 ∨ j = slot i 2 then {0} else univ
noncomputable def badWords (i : Fin 14) : Finset (Fin 42 → Fin 8) := Fintype.piFinset (allowed i)
noncomputable def P : ℕ[X] := ∑ a : Fin 8, X ^ a.val
noncomputable def Q (i : Fin 14) : ℕ[X] := ∑ a ∈ (univ.filter (fun a : Fin 8 => a.val < rankFloor i.val)), X ^ a.val

theorem Q_eq (i : Fin 14) : Q i = if i.val = 1 ∨ i.val = 8 then
    1 + X + X^2 + X^3 + X^4 else 1 + X + X^2 := by
  unfold Q rankFloor
  split_ifs <;> norm_num [Fin.sum_univ_succ, Finset.sum_filter] <;> ring

theorem special_card (i : Fin 14) : #{j : Fin 42 | ¬ special i j} = 39 := by
  revert i
  decide +kernel

theorem restricted_poly (i : Fin 14) :
    (∏ j : Fin 42, ∑ a ∈ allowed i j, (X : ℕ[X]) ^ a.val) = P ^ 39 * Q i := by
  have hfactor (j : Fin 42) :
      (∑ a ∈ allowed i j, (X : ℕ[X]) ^ a.val) =
        (if j = slot i 0 then Q i else 1) * (if special i j then 1 else P) := by
    by_cases h0 : j = slot i 0
    · simp [allowed, h0, special, Q]
    · by_cases h12 : j = slot i 1 ∨ j = slot i 2
      · simp [allowed, h0, h12, special]
      · simp [allowed, h0, h12, special, P]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hQ : (∏ j : Fin 42, if j = slot i 0 then Q i else 1) = Q i := by simp
  rw [hQ]
  have hP : (∏ j : Fin 42, if special i j then (1 : ℕ[X]) else P) = P ^ 39 := by
    rw [Finset.prod_ite]
    simp only [prod_const_one, one_mul, prod_const, special_card]
  rw [hP, mul_comm]

def sumDigits (d : Fin 42 → Fin 8) : ℕ := ∑ i, (d i).val

theorem card_bad_sum (i : Fin 14) (E : ℕ) :
    #{d ∈ badWords i | sumDigits d = E} = (P ^ 39 * Q i).coeff E := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (allowed i) (fun b : Fin 8 => b.val) E
  rw [restricted_poly] at h
  exact h

def evalP (B : ℕ) : ℕ := 1+B+B^2+B^3+B^4+B^5+B^6+B^7
def evalQ (i : Fin 14) (B : ℕ) : ℕ := if i.val = 1 ∨ i.val = 8 then 1+B+B^2+B^3+B^4 else 1+B+B^2

theorem eval_P (B : ℕ) : P.eval B = evalP B := by
  simp [P, evalP, Fin.sum_univ_succ]
  ring

theorem eval_Q (i : Fin 14) (B : ℕ) : (Q i).eval B = evalQ i B := by
  rw [Q_eq]
  split_ifs <;> simp_all [evalQ]

theorem coeff_lt (i : Fin 14) (E : ℕ) : (P^39*Q i).coeff E < 2^128 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ E) ?_
  rw [eval_mul, eval_pow, eval_P, eval_Q]
  unfold evalQ
  split <;> norm_num [evalP]

theorem coeff_eq (i : Fin 14) (E : ℕ) :
    (P^39*Q i).coeff E = (evalP (2^128)^39*evalQ i (2^128)) / (2^128)^E % 2^128 := by
  rw [← ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) E _ (coeff_lt i),
    eval_mul, eval_pow, eval_P, eval_Q]

def badCount (T : ℕ) (i : Fin 14) : ℕ :=
  (List.range 8).foldr (fun j a =>
    ((evalP (2^128)^39*evalQ i (2^128)) / (2^128)^(T-7+j) % 2^128) + a) 0

#time theorem badCount_199 (i : Fin 14) : badCount 199 i =
    if i.val = 1 ∨ i.val = 8 then 69955568807611825867574762043688 else 29756959616123883108233744232880 := by
  fin_cases i <;> decide +kernel
#time theorem badCount_200 (i : Fin 14) : badCount 200 i =
    if i.val = 1 ∨ i.val = 8 then 52300309978308840623335998836060 else 22062436680049562308975409015140 := by
  fin_cases i <;> decide +kernel



theorem mem_badWords (i : Fin 14) (d : Fin 42 → Fin 8) :
    d ∈ badWords i ↔ (d (slot i 0)).val < rankFloor i.val ∧ d (slot i 1) = 0 ∧ d (slot i 2) = 0 := by
  have h01 : slot i 0 ≠ slot i 1 := by intro h; have := congrArg Fin.val h; simp [slot] at this
  have h02 : slot i 0 ≠ slot i 2 := by intro h; have := congrArg Fin.val h; simp [slot] at this
  have h12 : slot i 1 ≠ slot i 2 := by intro h; have := congrArg Fin.val h; simp [slot] at this
  simp only [badWords, Fintype.mem_piFinset]
  constructor
  · intro h
    have h0 := h (slot i 0)
    have h1 := h (slot i 1)
    have h2 := h (slot i 2)
    simpa [allowed, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12] using And.intro h0 (And.intro h1 h2)
  · rintro ⟨h0,h1,h2⟩ j
    by_cases hj0 : j = slot i 0
    · subst j; simpa [allowed] using h0
    · by_cases hj1 : j = slot i 1
      · subst j; simp [allowed, hj0, h1]
      · by_cases hj2 : j = slot i 2
        · subst j; simp [allowed, hj0, h2]
        · simp [allowed, hj0, hj1, hj2]

def RankGood (n : ℕ) : Prop := ∀ i : Fin 14, rankFloor i.val ≤ n / 2^(9*i.val) % 512
instance (n : ℕ) : Decidable (RankGood n) := by unfold RankGood; infer_instance

theorem rank_bad_iff (d : Fin 42 → Fin 8) (i : Fin 14) :
    ¬ rankFloor i.val ≤ (finFunctionFinEquiv d).val / 2^(9*i.val) % 512 ↔ d ∈ badWords i := by
  rw [mem_badWords]
  have h0 := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv d) (slot i 0)
  have h1 := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv d) (slot i 1)
  have h2 := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv d) (slot i 2)
  simp only [Equiv.symm_apply_apply, slot, Fin.val_mk] at h0 h1 h2
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_ofNat, Nat.add_zero] at h0 h1 h2
  rw [pow_add] at h1 h2
  have hp : (8:ℕ)^(3*i.val) = 2^(9*i.val) := by
    calc (8:ℕ)^(3*i.val) = (2^3)^(3*i.val) := by norm_num
      _ = 2^(9*i.val) := by rw [← pow_mul]; congr 1; omega
  rw [hp] at h0 h1 h2
  rw [← Nat.div_div_eq_div_mul] at h1 h2
  have h1' : d (slot i 1) = 0 ↔ (d (slot i 1)).val = 0 := by simp
  have h2' : d (slot i 2) = 0 ↔ (d (slot i 2)).val = 0 := by simp
  rw [h1', h2']
  change (d (slot i 0)).val = _ at h0
  change (d (slot i 1)).val = (finFunctionFinEquiv d).val / 2^(9*i.val) / 8 % 8 at h1
  change (d (slot i 2)).val = (finFunctionFinEquiv d).val / 2^(9*i.val) / 64 % 8 at h2
  rw [h0,h1,h2]
  unfold rankFloor
  split <;> omega

theorem sumDigits_eq (d : Fin 42 → Fin 8) : sumDigits d = (lowerDigits (finFunctionFinEquiv d)).sum := by
  rw [lowerDigits_equiv, List.sum_ofFn]
  rfl

theorem card_bad_window (i : Fin 14) (T : ℕ) :
    #{d ∈ badWords i | sumDigits d ∈ Ico (T-7) (T-7+8)} = badCount T i := by
  rw [card_eq_sum_card_fiberwise (f := sumDigits) (t := Ico (T-7) (T-7+8))]
  · have hfib (E : ℕ) (hE : E ∈ Ico (T-7) (T-7+8)) :
      #{d ∈ {d ∈ badWords i | sumDigits d ∈ Ico (T-7) (T-7+8)} | sumDigits d = E} =
        #{d ∈ badWords i | sumDigits d = E} := by
      apply congrArg Finset.card
      ext d
      simp only [mem_filter]
      constructor
      · intro h; exact ⟨h.1.1,h.2⟩
      · intro h; exact ⟨⟨h.1,h.2 ▸ hE⟩,h.2⟩
    rw [sum_congr rfl hfib]
    simp_rw [card_bad_sum, coeff_eq]
    unfold badCount
    rw [range_foldr_eq_sum, sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
  · intro d hd
    exact (mem_filter.mp hd).2

theorem card_bad_accepted_le (T f : ℕ) (i : Fin 14) :
    #{d : Fin 42 → Fin 8 | accZ T f (statZ d) = true ∧ d ∈ badWords i} ≤ badCount T i := by
  rw [← card_bad_window i T]
  apply card_le_card
  intro d hd
  simp only [mem_filter, mem_univ, true_and] at hd ⊢
  refine ⟨hd.2, ?_⟩
  have ha := (accept_iffZ T f d).mpr hd.1
  unfold LowerAcceptZ LowerAccept at ha
  rw [sumDigits_eq, mem_Ico]
  exact ⟨by omega, by omega⟩



theorem card_good_ge (T f : ℕ) :
    #{d : Fin 42 → Fin 8 | accZ T f (statZ d) = true} - (∑ i : Fin 14, badCount T i) ≤
      #{d : Fin 42 → Fin 8 | accZ T f (statZ d) = true ∧ RankGood (finFunctionFinEquiv d)} := by
  classical
  let A : Finset (Fin 42 → Fin 8) := univ.filter fun d => accZ T f (statZ d) = true
  let B : Finset (Fin 42 → Fin 8) := univ.biUnion fun i : Fin 14 => A.filter fun d => d ∈ badWords i
  have hBA : B ⊆ A := by
    intro d hd
    obtain ⟨i,-,hi⟩ := mem_biUnion.mp hd
    exact (mem_filter.mp hi).1
  have hBc : B.card ≤ ∑ i : Fin 14, badCount T i := by
    calc B.card ≤ ∑ i : Fin 14, (A.filter fun d => d ∈ badWords i).card := card_biUnion_le
      _ ≤ ∑ i : Fin 14, badCount T i := by
        apply sum_le_sum
        intro i _
        simpa only [A, filter_filter] using card_bad_accepted_le T f i
  have hgood : (univ.filter fun d : Fin 42 → Fin 8 => accZ T f (statZ d) = true ∧ RankGood (finFunctionFinEquiv d)) = A \ B := by
    ext d
    simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_biUnion, A, B, exists_true_left]
    constructor
    · rintro ⟨ha,hg⟩
      refine ⟨ha, ?_⟩
      rintro ⟨i,-,hbad⟩
      exact ((rank_bad_iff d i).mpr hbad) (hg i)
    · rintro ⟨ha,hb⟩
      refine ⟨ha, ?_⟩
      intro i
      by_contra hi
      exact hb ⟨i,ha,(rank_bad_iff d i).mp hi⟩
  rw [hgood, card_sdiff_of_subset hBA]
  exact Nat.sub_le_sub_left hBc A.card

def LowerAcceptRank (T f n : ℕ) : Prop := LowerAcceptZ T f n ∧ RankGood n
instance (T f n : ℕ) : Decidable (LowerAcceptRank T f n) := by unfold LowerAcceptRank; infer_instance

theorem card_bitVec_eqRank (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptRank T f v.toNat).card =
      #{d : Fin 42 → Fin 8 | accZ T f (statZ d) = true ∧ RankGood (finFunctionFinEquiv d)} := by
  refine Finset.card_nbij' (fun v => finFunctionFinEquiv.symm ⟨v.toNat % 8 ^ 42, Nat.mod_lt _ (by positivity)⟩)
    (fun d => BitVec.ofNat 128 (finFunctionFinEquiv d)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1.1.1 (by norm_num))
    rw [← accept_iffZ, Equiv.apply_symm_apply]
    simpa only [hv', LowerAcceptRank] using hv
  · intro d hd
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num))]
    exact ⟨(accept_iffZ T f d).mpr hd.1,hd.2⟩
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1.1.1 (by norm_num))
    simp only [Equiv.apply_symm_apply, hv']
    exact BitVec.ofNat_toNat ..
  · intro d _
    simp only
    apply finFunctionFinEquiv.symm_apply_eq.mpr
    apply Fin.ext
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num)), Nat.mod_eq_of_lt (finFunctionFinEquiv d).isLt]

theorem card_lowerAcceptRank_ge (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptZ T f v.toNat).card - (∑ i : Fin 14, badCount T i) ≤
      (univ.filter fun v : BitVec 128 => LowerAcceptRank T f v.toNat).card := by
  rw [card_bitVec_eqZ,card_bitVec_eqRank]
  exact card_good_ge T f



def LowerAcceptS1Rank (T f n : ℕ) : Prop := LowerAcceptS1Z T f n ∧ RankGood (ofS1 n)
instance (T f n : ℕ) : Decidable (LowerAcceptS1Rank T f n) := by unfold LowerAcceptS1Rank; infer_instance

theorem lowerAcceptS1Rank_iff {m : ℕ} (hm : m < 2 ^ 128) (hs : SpareS1 m) (T f : ℕ) :
    LowerAcceptS1Rank T f m ↔ LowerAcceptRank T f (ofS1 m) := by
  unfold LowerAcceptS1Rank LowerAcceptRank
  rw [lowerAcceptS1Z_iff hm hs]

theorem card_lowerAcceptS1Rank (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Rank T f v.toNat).card =
      (univ.filter fun v : BitVec 128 => LowerAcceptRank T f v.toNat).card := by
  refine Finset.card_nbij' (fun v => BitVec.ofNat 128 (ofS1 v.toNat)) (fun v => BitVec.ofNat 128 (toS1 v.toNat))
    ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num))]
    exact (lowerAcceptS1Rank_iff v.isLt hv.1.1.2.1 T f).mp hv
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toS1_lt hv.1.1.1)]
    exact ⟨lowerAcceptS1Z_toS1 T f hv.1, by simpa only [ofS1_toS1 hv.1.1.1] using hv.2⟩
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num)),
      Nat.mod_eq_of_lt (toS1_lt (ofS1_lt _)), toS1_ofS1 v.isLt hv.1.1.2.1]
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (toS1_lt hv.1.1.1),
      Nat.mod_eq_of_lt ((ofS1_lt _).trans (by norm_num)), ofS1_toS1 hv.1.1.1]

theorem card_lowerAcceptS1Rank_ge (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAcceptS1Z T f v.toNat).card - (∑ i : Fin 14, badCount T i) ≤
      (univ.filter fun v : BitVec 128 => LowerAcceptS1Rank T f v.toNat).card := by
  rw [card_lowerAcceptS1Z,card_lowerAcceptS1Rank]
  exact card_lowerAcceptRank_ge T f

theorem card_lowerAcceptS1Rank_199_5 :
    86924063528333136971354894108426834 ≤
      (univ.filter fun v : BitVec 128 => LowerAcceptS1Rank 199 5 v.toNat).card := by
  have h := card_lowerAcceptS1Rank_ge 199 5
  rw [card_lowerAcceptS1Z_199_5] at h
  simp only [badCount_199] at h
  norm_num [Fin.sum_univ_succ] at h
  exact h

theorem card_lowerAcceptS1Rank_200_4 :
    72090332289016918256778319009782683 ≤
      (univ.filter fun v : BitVec 128 => LowerAcceptS1Rank 200 4 v.toNat).card := by
  have h := card_lowerAcceptS1Rank_ge 200 4
  rw [card_lowerAcceptS1Z_200_4] at h
  simp only [badCount_200] at h
  norm_num [Fin.sum_univ_succ] at h
  exact h

end ClaudeWCT.Numerics.LowerRank
end
