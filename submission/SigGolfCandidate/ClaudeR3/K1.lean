import SigGolfCandidate.ClaudeR3.E2
import SigGolfCandidate.ClaudeR3.K6

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqPA_ok0 : tqOk (posT tabM) 70938 0 (tqPA.getD 0 []) = true := by decide +kernel
theorem tqPA_ok1 : tqOk (posT tabM) 70938 1 (tqPA.getD 1 []) = true := by decide +kernel
theorem tqPA_ok2 : tqOk (posT tabM) 70938 2 (tqPA.getD 2 []) = true := by decide +kernel
theorem tqPA_ok3 : tqOk (posT tabM) 70938 3 (tqPA.getD 3 []) = true := by decide +kernel
theorem tqPA_ok4 : tqOk (posT tabM) 70938 4 (tqPA.getD 4 []) = true := by decide +kernel
theorem tqPA_ok5 : tqOk (posT tabM) 70938 5 (tqPA.getD 5 []) = true := by decide +kernel
theorem tqPA_ok6 : tqOk (posT tabM) 70938 6 (tqPA.getD 6 []) = true := by decide +kernel
theorem tqPA_ok7 : tqOk (posT tabM) 70938 7 (tqPA.getD 7 []) = true := by decide +kernel
theorem tqPA_ok8 : tqOk (posT tabM) 70938 8 (tqPA.getD 8 []) = true := by decide +kernel
theorem tqPA_ok9 : tqOk (posT tabM) 70938 9 (tqPA.getD 9 []) = true := by decide +kernel
theorem tqPA_ok10 : tqOk (posT tabM) 70938 10 (tqPA.getD 10 []) = true := by decide +kernel
theorem tqPA_ok11 : tqOk (posT tabM) 70938 11 (tqPA.getD 11 []) = true := by decide +kernel
theorem tqPA_ok12 : tqOk (posT tabM) 70938 12 (tqPA.getD 12 []) = true := by decide +kernel
theorem tqPA_ok13 : tqOk (posT tabM) 70938 13 (tqPA.getD 13 []) = true := by decide +kernel
theorem tqPA_ok14 : tqOk (posT tabM) 70938 14 (tqPA.getD 14 []) = true := by decide +kernel
theorem tqPA_ok15 : tqOk (posT tabM) 70938 15 (tqPA.getD 15 []) = true := by decide +kernel
theorem tqPA_ok16 : tqOk (posT tabM) 70938 16 (tqPA.getD 16 []) = true := by decide +kernel
theorem tqPA_ok17 : tqOk (posT tabM) 70938 17 (tqPA.getD 17 []) = true := by decide +kernel
theorem tqPA_ok18 : tqOk (posT tabM) 70938 18 (tqPA.getD 18 []) = true := by decide +kernel

theorem tqPA_all : ∀ j : ℕ, j < 19 → tqOk (posT tabM) 70938 j (tqPA.getD j []) = true
  | 0, _ => tqPA_ok0
  | 1, _ => tqPA_ok1
  | 2, _ => tqPA_ok2
  | 3, _ => tqPA_ok3
  | 4, _ => tqPA_ok4
  | 5, _ => tqPA_ok5
  | 6, _ => tqPA_ok6
  | 7, _ => tqPA_ok7
  | 8, _ => tqPA_ok8
  | 9, _ => tqPA_ok9
  | 10, _ => tqPA_ok10
  | 11, _ => tqPA_ok11
  | 12, _ => tqPA_ok12
  | 13, _ => tqPA_ok13
  | 14, _ => tqPA_ok14
  | 15, _ => tqPA_ok15
  | 16, _ => tqPA_ok16
  | 17, _ => tqPA_ok17
  | 18, _ => tqPA_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
