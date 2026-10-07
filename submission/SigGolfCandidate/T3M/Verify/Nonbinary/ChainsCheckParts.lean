import SigGolfCandidate.T3M.Verify.Nonbinary.ChainsLayout

namespace SigGolfCandidate.T3M.Nonbinary
/-- Join bounded kernel computations without normalizing an entire closed code window. -/
theorem check_range_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl

theorem tripleCheck_join {q : Nat}
    (hent : (List.range' 0 ((mx q + 1) ^ 3)).all (fun k => entCheck q k && s8Check q k) = true)
    (hblock : (List.range' 0 ((mx q + 1) ^ 2)).all
      (fun x => blockCheck q (x / (mx q + 1)) (x % (mx q + 1))) = true) :
    tripleCheck q = true := by
  unfold tripleCheck
  rw [List.range_eq_range', List.range_eq_range', hent, hblock]
  rfl
end SigGolfCandidate.T3M.Nonbinary
