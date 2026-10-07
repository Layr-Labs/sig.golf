import SigGolfCandidate.T3M.Verify.ChainRuns

namespace SigGolfCandidate.T3M
/-- Join bounded checks while keeping the closed code predicates opaque to unification. -/
theorem chain_all_range'_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem triCheck_add {t lo left right : Nat} (hdiv : left % 8 = 0)
    (hleft : triCheck t lo left = true)
    (hright : triCheck t (lo + left) right = true) :
    triCheck t lo (left + right) = true := by
  simp only [triCheck, Bool.and_eq_true] at hleft hright ⊢
  refine ⟨@chain_all_range'_add (entCheck t) lo left right hleft.1 hright.1, ?_⟩
  have hstart : (lo + left) / 8 = lo / 8 + left / 8 := by omega
  have hcount : (left + right) / 8 = left / 8 + right / 8 := by omega
  rw [hstart] at hright
  rw [hcount]
  exact @chain_all_range'_add (fun q => blkCheck t (q / 8) (q % 8))
    (lo / 8) (left / 8) (right / 8) hleft.2 hright.2
end SigGolfCandidate.T3M
