import SigGolfCandidate.ClaudeWCT.Numerics.CoverW1
import Mathlib.Data.FinEnum

namespace ClaudeWCT.Numerics.LowerCredit
open Finset Polynomial
set_option maxRecDepth 100000
def lowerDigits (n : ℕ) : List ℕ := (List.range 42).map fun i => n / 2 ^ (3 * i) % 8
def LowerAccept (T f n : ℕ) : Prop :=
  n < 2 ^ 126 ∧ (lowerDigits n).sum ≤ T ∧ T - (lowerDigits n).sum < 8 ∧
    f ≤ (lowerDigits n ++ [T - (lowerDigits n).sum]).count 6
instance (T f n : ℕ) : Decidable (LowerAccept T f n) := by unfold LowerAccept; infer_instance
def wt (a : ℕ) : ℕ := 64 * a + if a = 6 then 1 else 0
theorem sum_map_wt (l : List ℕ) : (l.map wt).sum = 64 * l.sum + l.count 6 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.count_cons]
    unfold wt
    by_cases h : a = 6
    · subst h; simp; omega
    · simp [h]; omega
theorem lowerDigits_equiv (d : Fin 42 → Fin 8) :
    lowerDigits (finFunctionFinEquiv d) = List.ofFn fun i => (d i : ℕ) := by
  apply List.ext_getElem
  · simp [lowerDigits]
  · intro i h1 h2
    have hi : i < 42 := by simpa [lowerDigits] using h1
    simp only [lowerDigits, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have h := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv d) ⟨i, hi⟩
    rw [Equiv.symm_apply_apply] at h
    rw [h, pow_mul]
    norm_num
def stat (d : Fin 42 → Fin 8) : ℕ := ∑ i, wt (d i)
theorem stat_eq (d : Fin 42 → Fin 8) :
    stat d = 64 * (lowerDigits (finFunctionFinEquiv d)).sum + (lowerDigits (finFunctionFinEquiv d)).count 6 := by
  rw [← sum_map_wt, lowerDigits_equiv, List.map_ofFn, List.sum_ofFn]
  rfl
def accE (T f E : ℕ) : Bool :=
  decide (E / 64 ≤ T ∧ T - E / 64 < 8 ∧ f ≤ E % 64 + if T - E / 64 = 6 then 1 else 0)
theorem equiv_lt (d : Fin 42 → Fin 8) : ((finFunctionFinEquiv d : Fin (8 ^ 42)) : ℕ) < 2 ^ 126 :=
  lt_of_lt_of_eq (finFunctionFinEquiv d).isLt (by norm_num)
theorem accept_list_iff (T f : ℕ) (L : List ℕ) (hlen : L.length = 42) (E : ℕ)
    (hE : E = 64 * L.sum + L.count 6) :
    (L.sum ≤ T ∧ T - L.sum < 8 ∧ f ≤ (L ++ [T - L.sum]).count 6) ↔
      (E / 64 ≤ T ∧ T - E / 64 < 8 ∧ f ≤ E % 64 + if T - E / 64 = 6 then 1 else 0) := by
  have hc : L.count 6 ≤ 42 := hlen ▸ List.count_le_length ..
  have h64 : E / 64 = L.sum := by omega
  have h64' : E % 64 = L.count 6 := by omega
  have hcount : (L ++ [T - L.sum]).count 6 = L.count 6 + if T - L.sum = 6 then 1 else 0 := by
    rw [List.count_append]
    by_cases h : T - L.sum = 6 <;> simp [h]
  rw [h64, h64', hcount]
theorem accept_iff (T f : ℕ) (d : Fin 42 → Fin 8) :
    LowerAccept T f (finFunctionFinEquiv d) ↔ accE T f (stat d) = true := by
  have hlen : (lowerDigits (finFunctionFinEquiv d)).length = 42 := by
    rw [lowerDigits_equiv, List.length_ofFn]
  unfold LowerAccept accE
  rw [decide_eq_true_iff, ← accept_list_iff T f _ hlen (stat d) (stat_eq d)]
  exact ⟨fun h => h.2, fun h => ⟨equiv_lt d, h⟩⟩
theorem accE_window {T f E : ℕ} (hT : 7 ≤ T) (h : accE T f E = true) :
    E ∈ Ico (64 * (T - 7)) (64 * (T - 7) + 512) := by
  unfold accE at h
  rw [decide_eq_true_iff] at h
  rw [mem_Ico]
  omega
def baseEval (B : ℕ) : ℕ :=
  B ^ wt 0 + B ^ wt 1 + B ^ wt 2 + B ^ wt 3 + B ^ wt 4 + B ^ wt 5 + B ^ wt 6 + B ^ wt 7
def lowerEval : ℕ := baseEval (2 ^ 128) ^ 42
def countCheck (T f count : ℕ) : Bool :=
  Nat.beq ((List.range 512).foldr (fun j s =>
    (if accE T f (64 * (T - 7) + j) = true then lowerEval / (2 ^ 128) ^ (64 * (T - 7) + j) % 2 ^ 128 else 0) + s) 0)
    count
noncomputable def basePoly : ℕ[X] := ∑ b : Fin 8, X ^ wt b
theorem card_stat_eq (E : ℕ) : #{d : Fin 42 → Fin 8 | stat d = E} = (basePoly ^ 42).coeff E := by
  have h := ClaudeWCT.Numerics.card_pi_sum_eq_coeff (fun _ : Fin 42 => (univ : Finset (Fin 8)))
    (fun b : Fin 8 => wt b) E
  rw [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at h
  exact h
theorem eval_basePoly (B : ℕ) : basePoly.eval B = baseEval B := by
  simp [basePoly, Fin.sum_univ_eight, baseEval]
theorem coeff_lt (i : ℕ) : (basePoly ^ 42).coeff i < 2 ^ 128 := by
  refine lt_of_le_of_lt (ClaudeWCT.Numerics.coeff_le_eval_one _ i) ?_
  rw [eval_pow, eval_basePoly]
  norm_num [baseEval]
theorem coeff_eq (E : ℕ) : (basePoly ^ 42).coeff E = lowerEval / (2 ^ 128) ^ E % 2 ^ 128 := by
  rw [← ClaudeWCT.Numerics.eval_div_pow_mod (by positivity) E _ coeff_lt, eval_pow, eval_basePoly]
  rfl
theorem range_foldr_eq_sum (h : ℕ → ℕ) (n : ℕ) :
    (List.range n).foldr (fun r s => h r + s) 0 = ∑ r ∈ Finset.range n, h r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldr_append, Finset.sum_range_succ]
    simp only [List.foldr_cons, List.foldr_nil, Nat.add_zero]
    have hshift : ∀ (l : List ℕ) (c : ℕ), l.foldr (fun r s => h r + s) c = l.foldr (fun r s => h r + s) 0 + c := by
      intro l c
      induction l with
      | nil => simp
      | cons a l ihl => simp only [List.foldr_cons, ihl]; omega
    rw [hshift, ih]
theorem card_bitVec_eq (T f : ℕ) :
    (univ.filter fun v : BitVec 128 => LowerAccept T f v.toNat).card =
      #{d : Fin 42 → Fin 8 | accE T f (stat d) = true} := by
  refine Finset.card_nbij' (fun v => finFunctionFinEquiv.symm ⟨v.toNat % 8 ^ 42, Nat.mod_lt _ (by positivity)⟩)
    (fun d => BitVec.ofNat 128 (finFunctionFinEquiv d)) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1 (by norm_num))
    rw [← accept_iff, Equiv.apply_symm_apply]
    simpa only [hv'] using hv
  · intro d hd
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hd ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num))]
    exact (accept_iff T f d).mpr hd
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    have hv' : v.toNat % 8 ^ 42 = v.toNat := Nat.mod_eq_of_lt (lt_of_lt_of_eq hv.1 (by norm_num))
    simp only [Equiv.apply_symm_apply, hv']
    exact BitVec.ofNat_toNat ..
  · intro d _
    simp only
    apply finFunctionFinEquiv.symm_apply_eq.mpr
    apply Fin.ext
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt ((equiv_lt d).trans (by norm_num)), Nat.mod_eq_of_lt (finFunctionFinEquiv d).isLt]
theorem card_lowerAccept_of_check (T f count : ℕ) (hT : 7 ≤ T) (hcheck : countCheck T f count = true) :
    (univ.filter fun v : BitVec 128 => LowerAccept T f v.toNat).card = count := by
  rw [card_bitVec_eq, card_eq_sum_card_fiberwise (f := stat) (t := Ico (64 * (T - 7)) (64 * (T - 7) + 512))
    (fun d hd => accE_window hT (by simpa using hd))]
  have hfib : ∀ E ∈ Ico (64 * (T - 7)) (64 * (T - 7) + 512),
      #{d ∈ {d : Fin 42 → Fin 8 | accE T f (stat d) = true} | stat d = E} =
        if accE T f E = true then lowerEval / (2 ^ 128) ^ E % 2 ^ 128 else 0 := by
    intro E _
    rw [filter_filter, ← coeff_eq, ← card_stat_eq]
    split_ifs with hE
    · exact congrArg Finset.card (filter_congr fun d _ => ⟨fun h => h.2, fun h => ⟨h ▸ hE, h⟩⟩)
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro d _ h
      exact hE (h.2 ▸ h.1)
  rw [sum_congr rfl hfib, sum_Ico_eq_sum_range, show 64 * (T - 7) + 512 - 64 * (T - 7) = 512 by omega,
    ← range_foldr_eq_sum (fun j => if accE T f (64 * (T - 7) + j) = true then
      lowerEval / (2 ^ 128) ^ (64 * (T - 7) + j) % 2 ^ 128 else 0)]
  exact Nat.eq_of_beq_eq_true hcheck
theorem check_197_4 : countCheck 197 4 140610462347261096978771217394878840 = true := by decide +kernel
theorem check_198_2 : countCheck 198 2 115572437016808486361789308152458664 = true := by decide +kernel
theorem check_197_0 : countCheck 197 0 143468572474466315422327516384120300 = true := by decide +kernel
theorem check_198_0 : countCheck 198 0 115663871454869880991236461657470944 = true := by decide +kernel
theorem card_lowerAccept_197_4 :
    (univ.filter fun v : BitVec 128 => LowerAccept 197 4 v.toNat).card = 140610462347261096978771217394878840 :=
  card_lowerAccept_of_check _ _ _ (by norm_num) check_197_4
theorem card_lowerAccept_198_2 :
    (univ.filter fun v : BitVec 128 => LowerAccept 198 2 v.toNat).card = 115572437016808486361789308152458664 :=
  card_lowerAccept_of_check _ _ _ (by norm_num) check_198_2
theorem card_lowerAccept_197_0 :
    (univ.filter fun v : BitVec 128 => LowerAccept 197 0 v.toNat).card = 143468572474466315422327516384120300 :=
  card_lowerAccept_of_check _ _ _ (by norm_num) check_197_0
theorem card_lowerAccept_198_0 :
    (univ.filter fun v : BitVec 128 => LowerAccept 198 0 v.toNat).card = 115663871454869880991236461657470944 :=
  card_lowerAccept_of_check _ _ _ (by norm_num) check_198_0
theorem check_198_4 : countCheck 198 4 113470737483767875195512089978341656 = true := by decide +kernel
theorem card_lowerAccept_198_4 :
    (univ.filter fun v : BitVec 128 => LowerAccept 198 4 v.toNat).card = 113470737483767875195512089978341656 :=
  card_lowerAccept_of_check _ _ _ (by norm_num) check_198_4
end ClaudeWCT.Numerics.LowerCredit
