import SigGolfCandidate.ClaudeWCT.Numerics.N600CapCount
import SigGolfCandidate.ClaudeWCT.Numerics.N600Price

namespace ClaudeWCT.Numerics.N600Cap
open Finset
open ClaudeWCT.WCT9 (Coord Child Rank)
noncomputable def honestLaw : (Coord → Child × Rank) → ENNReal := N600.uniformOn capSet
theorem capSet_nonempty : capSet.Nonempty := by
  rw [← card_pos, card_capSet]; unfold J; positivity
end ClaudeWCT.Numerics.N600Cap
