import SigGolfCandidate.ClaudeR3.E1
import SigGolfCandidate.ClaudeR3.D2

namespace ClaudeR3.Ev
open ClaudeR3.Tab (tabM)

def sidx (l m : ℕ) : ℕ := 16 + 15 * l - l * (l - 1) / 2 + (m - l)

noncomputable def tq0 (t : List (ℕ × ℕ)) (base j : ℕ) : ℕ := lsum (fun a => aB base j a) t
noncomputable def tq1 (t : List (ℕ × ℕ)) (base j l : ℕ) : ℕ := lsum (fun a => aB base j a * dig a.1 l) t
noncomputable def tq2 (t : List (ℕ × ℕ)) (base j l m : ℕ) : ℕ :=
  lsum (fun a => aB base j a * dig a.1 l * dig a.1 m) t

noncomputable def tqOk (t : List (ℕ × ℕ)) (base j : ℕ) (lit : List ℕ) : Bool :=
  (tq0 t base j == lit.getD 0 0) &&
    ((List.range 15).all fun l => tq1 t base j l == lit.getD (1 + l) 0) &&
    ((List.range 15).all fun l => (List.range (15 - l)).all fun i =>
      tq2 t base j l (l + i) == lit.getD (sidx l (l + i)) 0)

end ClaudeR3.Ev
