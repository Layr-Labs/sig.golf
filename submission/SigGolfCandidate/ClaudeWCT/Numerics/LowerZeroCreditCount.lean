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
#print axioms check_199_4
#time theorem check_199_5 : countCheckZ 199 5 87421058181341847220388848563308770 = true := by decide +kernel
#print axioms check_199_5
#time theorem check_200_4 : countCheckZ 200 4 72459682149134130685732695915636483 = true := by decide +kernel
#print axioms check_200_4
#print axioms accZ_window
#print axioms windowsZ_disjoint
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
#print axioms card_lowerAcceptS1Z_199_4
#print axioms card_lowerAcceptS1Z_199_5
#print axioms card_lowerAcceptS1Z_200_4
end ClaudeWCT.Numerics.LowerZeroCredit
