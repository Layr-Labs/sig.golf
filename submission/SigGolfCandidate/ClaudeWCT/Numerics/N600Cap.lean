import SigGolfCandidate.ClaudeWCT.Numerics.N600CapCount
import SigGolfCandidate.ClaudeWCT.Numerics.N600Price

namespace ClaudeWCT.Numerics.N600Cap
open Finset
open ClaudeWCT.WCT9 (Coord Child Rank)
noncomputable def honestLaw : (Coord → Child × Rank) → ENNReal := N600.uniformOn capSet
theorem capSet_nonempty : capSet.Nonempty := by
  rw [← card_pos, card_capSet]; unfold J; positivity
noncomputable def kappaHonest : ENNReal := ((N600.Q ^ 9 : ℕ) : ENNReal) / ((J : ℕ) : ENNReal)
theorem lawOK_honest : N600.LawOK honestLaw kappaHonest :=
  N600.lawOK_uniformOn' capSet capSet_nonempty (N600.Q ^ 9) J
    (N600.card_table (Fintype.card_fin 600) (Fintype.card_fin 128)) card_capSet (by unfold N600.Q J; norm_num)
end ClaudeWCT.Numerics.N600Cap
