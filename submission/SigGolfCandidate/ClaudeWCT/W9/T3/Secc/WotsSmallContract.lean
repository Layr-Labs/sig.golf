import SigGolfCandidate.ClaudeWCT.W9.T3.Secc.CaseCSplit

namespace ClaudeWCT.W9.T3.Security.Wots
open OracleComp OracleSpec OracleComp.EvalDist ENNReal
open SigGolfCandidate.T3 SigGolfCandidate.T3.Security
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Final
open SigGolfCandidate.T3.Security.Wots (signRatio digestClass)
noncomputable def nearPrice : ENNReal := 182
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
def CaseCSmallBound : Prop :=
  ∀ (adversary : AdversaryP) (q : Nat) (hq : q ≤ 2 ^ 127), 1 ≤ q → q ≤ SeccClosingW9.budgetSplit →
    Pr[fun z => QueryRecorded.CleanWin q z.1 ∧ CaseC.CaseCFreshPinned adversary z |
        SeccLaw.completedExperiment adversary q hq] ≤
      (1 + SeccClosingW9.cacheRate) / 2 ^ 128 * SeccLaw.expectedCharge adversary q hq digestClass +
        ((signRatio * q : Nat) : ENNReal) * SeccClosingW9.excessRate / 2 ^ 128 + nearTerm q + BPair.pairTerm q +
        (2 : ENNReal)⁻¹ ^ 700
theorem caseCSmallBound_iff :
    CaseCSmallBound ↔ CaseC.CaseCSmallBound CaseC.CaseCFreshPinned nearTerm BPair.pairTerm := Iff.rfl
end ClaudeWCT.W9.T3.Security.Wots
