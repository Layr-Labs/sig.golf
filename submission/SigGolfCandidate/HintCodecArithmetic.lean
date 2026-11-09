import SigGolfCandidate.LegacyCodec
set_option autoImplicit false
namespace HintResearch
/-- Research codec; unused codes use the odd-floor gap, preserving 13-bit logical hints. -/
def compress (h : Nat) : Nat :=
  if 520 ≤ h ∧ h < 854 then 3762 + (h-520) else 418 * (h / 484 / 2) + h % 484
def expand (j : Nat) : Nat :=
  if j < 3762 then 968 * (j / 418) + j % 418 else 520 + (j-3762)
 theorem compress_expand (j : Nat) (hj : j < 4096) : compress (expand j) = j := by
  have hm := Nat.mod_lt j (by decide : 0 < 418)
  have hd := Nat.mod_add_div j 418
  unfold compress expand
  split_ifs <;> omega
 theorem expand_compress (h : Nat) (hh : h < 8192) (he : h / 484 % 2 = 0) (hr : h % 484 < 418) :
    expand (compress h) = h := by
  have hd := Nat.mod_add_div h 484
  have he' := Nat.mod_add_div (h / 484) 2
  unfold compress expand
  split_ifs <;> omega
 theorem compress_bound (h : Nat) (hh : h < 7744) (hr : h % 484 < 418) : compress h < 4096 := by
  unfold compress
  split_ifs <;> omega
 theorem expand_bound (j : Nat) (hj : j < 4096) : expand j < 2^13 := by
  have hm := Nat.mod_lt j (by decide : 0 < 418)
  unfold expand
  split_ifs <;> omega
theorem x_slices (a j u : Nat) (ha : a < 2^24) (hj : j < 2^12) (hu : u < 2) :
    (a+j*2^24+u*2^36)%2^24=a ∧
    (a+j*2^24+u*2^36)/2^24%2^12=j ∧
    (a+j*2^24+u*2^36)/2^36=u := by
  simp only [Nat.reducePow] at *
  omega
 theorem top_slices (t u v a : Nat) (ht : t < 2^24) (hu : u < 2) (hv : v < 2^52) (ha : a < 2^24) :
    let z := t+u*2^24+v*2^25+a*2^77
    z%2^24=t ∧ z/2^24%2=u ∧ z/2^25%2^52=v ∧ z/2^77%2^24=a := by
  simp only [Nat.reducePow] at *
  omega
end HintResearch

set_option autoImplicit false
namespace HintPolicyResearch
def one : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4, 4, 6, 6, 6, 8, 8, 10, 10, 10, 12, 12, 14, 14]
def two : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10, 11, 12, 13, 14, 14, 15, 16, 17, 18]
theorem one_even (r : Nat) (h : one.getD r 301 < 22) : one.getD r 301 % 2 = 0 := by
  have hl : one.length = 54 := by decide
  by_cases hr : r < 54
  · have hf : ∀ i : Fin 54, one.getD i.val 301 % 2 = 0 := by decide +kernel
    exact hf ⟨r,hr⟩
  · rw [List.getD_eq_default _ _ (by omega)] at h
    omega
theorem two_le (r : Nat) (h : two.getD r 301 < 22) : two.getD r 301 ≤ 18 := by
  have hl : two.length = 40 := by decide
  by_cases hr : r < 40
  · have hf : ∀ i : Fin 40, two.getD i.val 301 ≤ 18 := by decide +kernel
    exact hf ⟨r,hr⟩
  · rw [List.getD_eq_default _ _ (by omega)] at h
    omega
theorem normal_of_floor_bounds (h : Nat) (hh : h < 7744) (he : h / 484 % 2 = 0)
    (h2 : h / 22 % 22 ≤ 18) : HintResearch.expand (HintResearch.compress h % 2^12) = h % 2^13 := by
  have hd : h % 484 = h % 22 + 22 * (h / 22 % 22) := by
    rw [show (484:Nat) = 22*22 from rfl, Nat.mod_mul]
  have hr : h % 484 < 418 := by have hm := Nat.mod_lt h (by decide : 0 < 22); omega
  have hc : HintResearch.compress h < 2^12 := HintResearch.compress_bound h hh hr
  rw [Nat.mod_eq_of_lt hc, HintResearch.expand_compress h (by omega) he hr,
    Nat.mod_eq_of_lt (by omega : h < 2^13)]
end HintPolicyResearch
