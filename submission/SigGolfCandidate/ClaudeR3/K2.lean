import SigGolfCandidate.ClaudeR3.E2
import SigGolfCandidate.ClaudeR3.K1

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqNA_ok0 : tqOk (negT tabM) 70938 0 (tqNA.getD 0 []) = true := by decide +kernel
theorem tqNA_ok1 : tqOk (negT tabM) 70938 1 (tqNA.getD 1 []) = true := by decide +kernel
theorem tqNA_ok2 : tqOk (negT tabM) 70938 2 (tqNA.getD 2 []) = true := by decide +kernel
theorem tqNA_ok3 : tqOk (negT tabM) 70938 3 (tqNA.getD 3 []) = true := by decide +kernel
theorem tqNA_ok4 : tqOk (negT tabM) 70938 4 (tqNA.getD 4 []) = true := by decide +kernel
theorem tqNA_ok5 : tqOk (negT tabM) 70938 5 (tqNA.getD 5 []) = true := by decide +kernel
theorem tqNA_ok6 : tqOk (negT tabM) 70938 6 (tqNA.getD 6 []) = true := by decide +kernel
theorem tqNA_ok7 : tqOk (negT tabM) 70938 7 (tqNA.getD 7 []) = true := by decide +kernel
theorem tqNA_ok8 : tqOk (negT tabM) 70938 8 (tqNA.getD 8 []) = true := by decide +kernel
theorem tqNA_ok9 : tqOk (negT tabM) 70938 9 (tqNA.getD 9 []) = true := by decide +kernel
theorem tqNA_ok10 : tqOk (negT tabM) 70938 10 (tqNA.getD 10 []) = true := by decide +kernel
theorem tqNA_ok11 : tqOk (negT tabM) 70938 11 (tqNA.getD 11 []) = true := by decide +kernel
theorem tqNA_ok12 : tqOk (negT tabM) 70938 12 (tqNA.getD 12 []) = true := by decide +kernel
theorem tqNA_ok13 : tqOk (negT tabM) 70938 13 (tqNA.getD 13 []) = true := by decide +kernel
theorem tqNA_ok14 : tqOk (negT tabM) 70938 14 (tqNA.getD 14 []) = true := by decide +kernel
theorem tqNA_ok15 : tqOk (negT tabM) 70938 15 (tqNA.getD 15 []) = true := by decide +kernel
theorem tqNA_ok16 : tqOk (negT tabM) 70938 16 (tqNA.getD 16 []) = true := by decide +kernel
theorem tqNA_ok17 : tqOk (negT tabM) 70938 17 (tqNA.getD 17 []) = true := by decide +kernel
theorem tqNA_ok18 : tqOk (negT tabM) 70938 18 (tqNA.getD 18 []) = true := by decide +kernel

theorem tqNA_all : ∀ j : ℕ, j < 19 → tqOk (negT tabM) 70938 j (tqNA.getD j []) = true
  | 0, _ => tqNA_ok0
  | 1, _ => tqNA_ok1
  | 2, _ => tqNA_ok2
  | 3, _ => tqNA_ok3
  | 4, _ => tqNA_ok4
  | 5, _ => tqNA_ok5
  | 6, _ => tqNA_ok6
  | 7, _ => tqNA_ok7
  | 8, _ => tqNA_ok8
  | 9, _ => tqNA_ok9
  | 10, _ => tqNA_ok10
  | 11, _ => tqNA_ok11
  | 12, _ => tqNA_ok12
  | 13, _ => tqNA_ok13
  | 14, _ => tqNA_ok14
  | 15, _ => tqNA_ok15
  | 16, _ => tqNA_ok16
  | 17, _ => tqNA_ok17
  | 18, _ => tqNA_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
