import SigGolfCandidate.ClaudeR3.E2
import SigGolfCandidate.ClaudeR3.K3

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqNB_ok0 : tqOk (negT tabM) 0 0 (tqNB.getD 0 []) = true := by decide +kernel
theorem tqNB_ok1 : tqOk (negT tabM) 0 1 (tqNB.getD 1 []) = true := by decide +kernel
theorem tqNB_ok2 : tqOk (negT tabM) 0 2 (tqNB.getD 2 []) = true := by decide +kernel
theorem tqNB_ok3 : tqOk (negT tabM) 0 3 (tqNB.getD 3 []) = true := by decide +kernel
theorem tqNB_ok4 : tqOk (negT tabM) 0 4 (tqNB.getD 4 []) = true := by decide +kernel
theorem tqNB_ok5 : tqOk (negT tabM) 0 5 (tqNB.getD 5 []) = true := by decide +kernel
theorem tqNB_ok6 : tqOk (negT tabM) 0 6 (tqNB.getD 6 []) = true := by decide +kernel
theorem tqNB_ok7 : tqOk (negT tabM) 0 7 (tqNB.getD 7 []) = true := by decide +kernel
theorem tqNB_ok8 : tqOk (negT tabM) 0 8 (tqNB.getD 8 []) = true := by decide +kernel
theorem tqNB_ok9 : tqOk (negT tabM) 0 9 (tqNB.getD 9 []) = true := by decide +kernel
theorem tqNB_ok10 : tqOk (negT tabM) 0 10 (tqNB.getD 10 []) = true := by decide +kernel
theorem tqNB_ok11 : tqOk (negT tabM) 0 11 (tqNB.getD 11 []) = true := by decide +kernel
theorem tqNB_ok12 : tqOk (negT tabM) 0 12 (tqNB.getD 12 []) = true := by decide +kernel
theorem tqNB_ok13 : tqOk (negT tabM) 0 13 (tqNB.getD 13 []) = true := by decide +kernel
theorem tqNB_ok14 : tqOk (negT tabM) 0 14 (tqNB.getD 14 []) = true := by decide +kernel
theorem tqNB_ok15 : tqOk (negT tabM) 0 15 (tqNB.getD 15 []) = true := by decide +kernel
theorem tqNB_ok16 : tqOk (negT tabM) 0 16 (tqNB.getD 16 []) = true := by decide +kernel
theorem tqNB_ok17 : tqOk (negT tabM) 0 17 (tqNB.getD 17 []) = true := by decide +kernel
theorem tqNB_ok18 : tqOk (negT tabM) 0 18 (tqNB.getD 18 []) = true := by decide +kernel

theorem tqNB_all : ∀ j : ℕ, j < 19 → tqOk (negT tabM) 0 j (tqNB.getD j []) = true
  | 0, _ => tqNB_ok0
  | 1, _ => tqNB_ok1
  | 2, _ => tqNB_ok2
  | 3, _ => tqNB_ok3
  | 4, _ => tqNB_ok4
  | 5, _ => tqNB_ok5
  | 6, _ => tqNB_ok6
  | 7, _ => tqNB_ok7
  | 8, _ => tqNB_ok8
  | 9, _ => tqNB_ok9
  | 10, _ => tqNB_ok10
  | 11, _ => tqNB_ok11
  | 12, _ => tqNB_ok12
  | 13, _ => tqNB_ok13
  | 14, _ => tqNB_ok14
  | 15, _ => tqNB_ok15
  | 16, _ => tqNB_ok16
  | 17, _ => tqNB_ok17
  | 18, _ => tqNB_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
