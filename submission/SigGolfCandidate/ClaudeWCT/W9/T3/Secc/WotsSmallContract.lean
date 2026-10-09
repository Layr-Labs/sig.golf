import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSplit
import SigGolfCandidate.ClaudeWCT.W9.New.G6.PairFinal

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Security.Wots (signRatio digestClass)
noncomputable def nearPrice : ENNReal := 150
noncomputable def nearTermSlots (slots : Nat) (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (nearPrice * q / 2 ^ 128 + slots * (signRatio * q : Nat) * SeccClosingW9.cacheRate / 2 ^ 128 +
      slots * (2 : ENNReal)⁻¹ ^ 700)
noncomputable def nearTerm (q : Nat) : ENNReal :=
  (q : ENNReal) * ((2 ^ 128 - q : Nat) : ENNReal)⁻¹ *
    (nearPrice * q / 2 ^ 128 + 63 * (signRatio * q : Nat) * SeccClosingW9.cacheRate / 2 ^ 128 +
      63 * (2 : ENNReal)⁻¹ ^ 700)
theorem nearTerm_eq_slots (q : Nat) : nearTerm q = nearTermSlots 63 q := by
  unfold nearTerm nearTermSlots
  norm_num
/-- Small case-C bound on the runs without FTS overflow (`WPair.NoOverflow`, campaign X1 stage A); the overflow
mass `2^-137` is charged to `SeccClosingW9.smallAbsolute` in `cleanWin_le_cases` / `small_route`. -/
def CaseCSmallBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosingW9.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z ∧ WPair.NoOverflow adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosingW9.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq digestClass +
        (q : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700
theorem caseCSmallBound_iff :
    CaseCSmallBound ↔ CaseC.CaseCSmallBound CaseC.CaseCFreshPinned WPair.NoOverflow nearTerm BPair.pairTerm := Iff.rfl
end ClaudeWCT.W9.T3.Security.Wots
