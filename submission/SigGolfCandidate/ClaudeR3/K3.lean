import SigGolfCandidate.ClaudeR3.E2
import SigGolfCandidate.ClaudeR3.K2

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

set_option maxRecDepth 100000
theorem tqPB_ok0 : tqOk (posT tabM) 0 0 (tqPB.getD 0 []) = true := by decide +kernel
theorem tqPB_ok1 : tqOk (posT tabM) 0 1 (tqPB.getD 1 []) = true := by decide +kernel
theorem tqPB_ok2 : tqOk (posT tabM) 0 2 (tqPB.getD 2 []) = true := by decide +kernel
theorem tqPB_ok3 : tqOk (posT tabM) 0 3 (tqPB.getD 3 []) = true := by decide +kernel
theorem tqPB_ok4 : tqOk (posT tabM) 0 4 (tqPB.getD 4 []) = true := by decide +kernel
theorem tqPB_ok5 : tqOk (posT tabM) 0 5 (tqPB.getD 5 []) = true := by decide +kernel
theorem tqPB_ok6 : tqOk (posT tabM) 0 6 (tqPB.getD 6 []) = true := by decide +kernel
theorem tqPB_ok7 : tqOk (posT tabM) 0 7 (tqPB.getD 7 []) = true := by decide +kernel
theorem tqPB_ok8 : tqOk (posT tabM) 0 8 (tqPB.getD 8 []) = true := by decide +kernel
theorem tqPB_ok9 : tqOk (posT tabM) 0 9 (tqPB.getD 9 []) = true := by decide +kernel
theorem tqPB_ok10 : tqOk (posT tabM) 0 10 (tqPB.getD 10 []) = true := by decide +kernel
theorem tqPB_ok11 : tqOk (posT tabM) 0 11 (tqPB.getD 11 []) = true := by decide +kernel
theorem tqPB_ok12 : tqOk (posT tabM) 0 12 (tqPB.getD 12 []) = true := by decide +kernel
theorem tqPB_ok13 : tqOk (posT tabM) 0 13 (tqPB.getD 13 []) = true := by decide +kernel
theorem tqPB_ok14 : tqOk (posT tabM) 0 14 (tqPB.getD 14 []) = true := by decide +kernel
theorem tqPB_ok15 : tqOk (posT tabM) 0 15 (tqPB.getD 15 []) = true := by decide +kernel
theorem tqPB_ok16 : tqOk (posT tabM) 0 16 (tqPB.getD 16 []) = true := by decide +kernel
theorem tqPB_ok17 : tqOk (posT tabM) 0 17 (tqPB.getD 17 []) = true := by decide +kernel
theorem tqPB_ok18 : tqOk (posT tabM) 0 18 (tqPB.getD 18 []) = true := by decide +kernel

theorem tqPB_all : ∀ j : ℕ, j < 19 → tqOk (posT tabM) 0 j (tqPB.getD j []) = true
  | 0, _ => tqPB_ok0
  | 1, _ => tqPB_ok1
  | 2, _ => tqPB_ok2
  | 3, _ => tqPB_ok3
  | 4, _ => tqPB_ok4
  | 5, _ => tqPB_ok5
  | 6, _ => tqPB_ok6
  | 7, _ => tqPB_ok7
  | 8, _ => tqPB_ok8
  | 9, _ => tqPB_ok9
  | 10, _ => tqPB_ok10
  | 11, _ => tqPB_ok11
  | 12, _ => tqPB_ok12
  | 13, _ => tqPB_ok13
  | 14, _ => tqPB_ok14
  | 15, _ => tqPB_ok15
  | 16, _ => tqPB_ok16
  | 17, _ => tqPB_ok17
  | 18, _ => tqPB_ok18
  | _ + 19, h => absurd h (by omega)

end ClaudeR3.Ev
