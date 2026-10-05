import SigGolfCandidate.W9Machine.WctN600Data
import SigGolfCandidate.ClaudeWCT.WCT9.Codebook

section


namespace W9Machine.N600
def C1RanksEq : Prop := originalRanks = ClaudeWCT.WCT9.codeRanks
def C1CostsEq : Prop := rankCosts = ClaudeWCT.WCT9.routineCosts
def C1EmbedEq : Prop := embed = ClaudeWCT.WCT9.embed
def C1RankCostEq : Prop := rankCost = ClaudeWCT.WCT9.routineCost
def C1WordsEq : Prop :=
  originalRanks.map (fun r => (ClaudeWCT.WCT9.compositions 4 7 6).getD r []) =
    ClaudeWCT.WCT9.codeWords
end W9Machine.N600
end

section

namespace W9Machine.N600
set_option maxRecDepth 100000
theorem originalRanks_eq_c1 : C1RanksEq := rfl
theorem rankCosts_eq_c1 : C1CostsEq := rfl
theorem embed_eq_c1 : C1EmbedEq := by
  funext rank
  apply Fin.ext
  change originalRanks.getD rank.val 0 = _
  rw [show originalRanks = ClaudeWCT.WCT9.codeRanks from originalRanks_eq_c1,
    List.getD_eq_getElem _ _ (by rw [ClaudeWCT.WCT9.codeRanks_length]; exact rank.isLt)]
  rfl
theorem rankCost_eq_c1 : C1RankCostEq := by
  funext rank
  change rankCosts.getD rank.val 0 = _
  rw [show rankCosts = ClaudeWCT.WCT9.routineCosts from rankCosts_eq_c1,
    List.getD_eq_getElem _ _ (by rw [ClaudeWCT.WCT9.routineCosts_length]; exact rank.isLt)]
  rfl
theorem codeWords_eq_c1 : C1WordsEq := by
  change originalRanks.map _ = _
  rw [show originalRanks = ClaudeWCT.WCT9.codeRanks from originalRanks_eq_c1]
  exact ClaudeWCT.WCT9.codeRanks_map
end W9Machine.N600
end
