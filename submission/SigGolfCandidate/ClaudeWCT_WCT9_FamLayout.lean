import SigGolfCandidate.ClaudeWCT_WCT9_Correctness

/-! # Seed-family layout: generic facts (r3-lean-seedfam, family port P7)

Facts about the layout of `Correctness` (`famGrp`, `famBase`, `famSize`, `famStride`, `famOf`, `famPoint`) used by the
security bridge (CanonGraph, large route). All proofs here go through the generic layout facts of `Correctness`
(`famGrp_pos`, `famStride_ge`, ...) except `famSize_pos`, which must be re-proved at the v6 flip. -/

namespace ClaudeWCT.WCT9
open SigGolfCandidate SigGolfCandidate.T3

/-- Every family has a coefficient (top 24, lower `5 r + 3 ≥ 3`). -/
theorem famSize_pos (lay : Layer) (f : Nat) : 0 < famSize lay f := by
  unfold famSize; split_ifs
  · decide
  · omega

theorem famSize_lt_58 (lay : Layer) (f : Nat) : famSize lay f < 58 := by
  have := famSize_le_base lay f; have := famBase_le lay; omega

theorem famOf_le (lay : Layer) (leaf : Nat) : famOf lay leaf ≤ leaf := Nat.div_le_self _ _

theorem famOf_lt {lay : Layer} {leaf : Nat} (h : leaf < 4096) : famOf lay leaf < 4096 :=
  lt_of_le_of_lt (famOf_le lay leaf) h

/-- `r·s + a` determines `(r, a)` when `a < s`. -/
theorem mul_add_inj {r r' s a a' : Nat} (ha : a < s) (ha' : a' < s) (h : r * s + a = r' * s + a') :
    r = r' ∧ a = a' := by
  rcases Nat.lt_or_ge r r' with hlt | hge
  · exfalso
    have : r * s + s ≤ r' * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt
    omega
  · rcases Nat.lt_or_ge r' r with hlt' | hge'
    · exfalso
      have : r' * s + s ≤ r * s := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hlt'
      omega
    · have hrr : r = r' := by omega
      subst hrr
      exact ⟨rfl, by omega⟩

/-- Within a family the evaluation points of the address slots `i < 58` are distinct. -/
theorem famPoint_inj {lay : Layer} {l l' i i' : Nat} (hi : i < 58) (hi' : i' < 58)
    (hf : famOf lay l = famOf lay l') (h : famPoint lay l i = famPoint lay l' i') : l = l' ∧ i = i' := by
  have hg := famGrp_pos lay
  have hm : l % famGrp lay < famGrp lay := Nat.mod_lt _ hg
  have hm' : l' % famGrp lay < famGrp lay := Nat.mod_lt _ hg
  have hreal : ∀ r, r < famGrp lay → r * famStride lay + famStride lay ≤ famGrp lay * famStride lay := by
    intro r hr
    rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hr
  have hlt : ∀ k, k < 58 → (lay = 0 ∨ k < chainCount lay) → k < famStride lay := by
    intro k hk hc
    rcases hc with h0 | h0
    · subst h0; have := famStride_top; omega
    · have := famStride_ge lay; omega
  have hjunk : ∀ k, ¬(lay = 0 ∨ k < chainCount lay) → chainCount lay ≤ k := by
    intro k hk; by_contra hc; exact hk (Or.inr (by omega))
  have hrr : l % famGrp lay = l' % famGrp lay ∧ i = i' := by
    unfold famPoint at h
    split_ifs at h with h1 h2 h2
    · have a1 := hlt i hi h1
      have a2 := hlt i' hi' h2
      exact mul_add_inj a1 a2 (by omega : l % famGrp lay * famStride lay + i =
        l' % famGrp lay * famStride lay + i')
    · have a1 := hlt i hi h1; have := hreal _ hm; omega
    · have a2 := hlt i' hi' h2; have := hreal _ hm'; omega
    · have c1 := hjunk i h1
      have c2 := hjunk i' h2
      obtain ⟨e1, e2⟩ := mul_add_inj (s := 58 - chainCount lay) (a := i - chainCount lay)
        (a' := i' - chainCount lay) (by omega) (by omega) (by omega : l % famGrp lay * (58 - chainCount lay) +
          (i - chainCount lay) = l' % famGrp lay * (58 - chainCount lay) + (i' - chainCount lay))
      exact ⟨e1, by omega⟩
  refine ⟨?_, hrr.2⟩
  have e := Nat.div_add_mod l (famGrp lay)
  have e' := Nat.div_add_mod l' (famGrp lay)
  unfold famOf at hf
  rw [← e, ← e', hf, hrr.1]

end ClaudeWCT.WCT9
