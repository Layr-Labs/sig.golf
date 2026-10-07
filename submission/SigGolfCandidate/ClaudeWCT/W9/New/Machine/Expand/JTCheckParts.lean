import SigGolfCandidate.ClaudeWCT.W9.New.Machine.Expand.RoutineCheck2

namespace ClaudeWCT.W9.Machine.Expand
/-- Compose bounded kernel checks without reducing the entire jump-table window at once. -/
theorem all_range'_add {p : Nat → Bool} {lo left right : Nat}
    (hleft : (List.range' lo left).all p = true)
    (hright : (List.range' (lo + left) right).all p = true) :
    (List.range' lo (left + right)).all p = true := by
  rw [← List.range'_append_1, List.all_append, hleft, hright]
  rfl
end ClaudeWCT.W9.Machine.Expand
