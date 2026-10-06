import SigGolfCandidate.Rv.Sound

/- A symbolic run consumes at most one code word per unit of fuel and stops
   at a branch, jump, or ECALL. A finite prefix therefore suffices for the
   unchanged consumer blocks; no old whole-image CodeAt premise is needed. -/
namespace SigGolfCandidate.Rv
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64
set_option autoImplicit false

theorem symRunAux_take (cfg : Config) (code : List (BitVec 32)) (pc : Word)
    (fuel : Nat) (sigma : SymState) :
    symRunAux cfg (code.take fuel) pc fuel sigma = symRunAux cfg code pc fuel sigma := by
  induction fuel generalizing code pc sigma with
  | zero => cases code <;> rfl
  | succ fuel ih =>
    cases code with
    | nil => rfl
    | cons word rest =>
      simp only [List.take_succ_cons, symRunAux]
      cases hd : decodeInstruction word with
      | none => simp only [hd]
      | some ins =>
        simp only [hd]
        by_cases he : isEcall ins = true
        · simp only [he, if_true]
        · have hn : isEcall ins = false := Bool.eq_false_iff.mpr he
          simp only [hn, Bool.false_eq_true, if_false]
          cases hc : classify ins with
          | none => simp only [hc]
          | some micro =>
            simp only [hc]
            cases hm : symMicro cfg pc sigma micro with
            | none => simp only [hm]
            | some next =>
              obtain ⟨sigma', dest⟩ := next
              cases dest with
              | none => simp only [hm, ih]
              | some target => simp only [hm]

theorem symRun_take (cfg : Config) (code : List (BitVec 32)) (pc : Word) (fuel : Nat) :
    symRun cfg (code.take fuel) pc fuel = symRun cfg code pc fuel :=
  symRunAux_take cfg code pc fuel SymState.init

theorem symRun_prefix (cfg : Config) (code : List (BitVec 32)) (pc : Word)
    (fuel size : Nat) (hf : fuel ≤ size) :
    symRun cfg (code.take size) pc fuel = symRun cfg code pc fuel := by
  rw [← symRun_take cfg (code.take size) pc fuel, List.take_take,
    Nat.min_eq_left hf, symRun_take]

theorem symRun_prefix_sound {im : Image} {cfg : Config} {code : List (BitVec 32)}
    {pc : Word} {fuel size : Nat} {result : Result}
    (hr : symRun cfg code pc fuel = some result) (hf : fuel ≤ size)
    (hc : CodeAt im pc (code.take size)) (s : MachineState)
    (hp : s.pc = pc) (ho : result.obligs s) :
    Steps im s result.steps result.cycles (result.toState s) := by
  have hrun : symRun cfg (code.take size) pc fuel = some result := by
    rw [symRun_prefix cfg code pc fuel size hf]
    exact hr
  exact symRun_sound hrun hc s hp ho

theorem symRun_prefix_ecall {im : Image} {cfg : Config} {code : List (BitVec 32)}
    {pc : Word} {fuel size : Nat} {result : Result}
    (hr : symRun cfg code pc fuel = some result) (hf : fuel ≤ size)
    (hc : CodeAt im pc (code.take size)) (s : MachineState)
    (ho : result.obligs s) (hs : result.stop = .ecall) :
    fetch im (result.toState s) = some (.base .ECALL) := by
  have hrun : symRun cfg (code.take size) pc fuel = some result := by
    rw [symRun_prefix cfg code pc fuel size hf]
    exact hr
  exact symRun_ecall hrun hc s ho hs

#print axioms symRun_prefix_sound
#print axioms symRun_prefix_ecall

end SigGolfCandidate.Rv
