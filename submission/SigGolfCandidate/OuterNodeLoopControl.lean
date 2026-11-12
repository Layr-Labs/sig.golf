import SigGolfCandidate.FtsCode
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeLoopControl
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind

theorem loop_sim {im : Image} {sk : BitVec 256} (hi : Bool) (b cap checkCost : Nat)
    (pre right : List UInt8) (At : Nat → MachineState → Prop) (Hashed : Nat → HashOutput → MachineState → Prop)
    (Out : Nat × HashOutput → MachineState → Prop)
    (htrial : ∀ {β : Type} n u,At n u → n<cap → ∀ (W : Nat) (f : HashOutput → M β) (Q : β → MachineState → Prop),
      (∀ a t,Hashed n a t → TBSim im sk t W (f a) Q) →
      TBSim im sk u (9+W) (publicHash (trialInput pre n right) >>= f) Q)
    (hfinish : ∀ n a u,Hashed n a u → n<cap → zeroOkH hi b a=true →
      TBSim im sk u (checkCost+9) (pure (n,a)) Out)
    (hretry : ∀ n a u,Hashed n a u → ¬zeroOkH hi b a=true → n+1<cap →
      ∃ t,Steps im u (checkCost+3) (checkCost+3) t ∧ At (n+1) t)
    (hexhaust : ∀ n a u,Hashed n a u → ¬zeroOkH hi b a=true → n+1=cap →
      TBSim im sk u (checkCost+13) (pure (n,a)) Out) :
    ∀ fuel n u,At n u → n+fuel+1=cap →
      TBSim im sk u ((checkCost+12)*fuel+(checkCost+22)) (searchH hi b pre right fuel n) Out := by
  intro fuel
  induction fuel with
  | zero =>
    intro n u hu hcap
    rw [searchH]
    refine (htrial n u hu (by omega) (checkCost+13) (fun a=>pure (n,a)) Out (fun a t ht=>?_)).mono (by omega) (by intros;assumption)
    by_cases hz : zeroOkH hi b a=true
    · exact (hfinish n a t ht (by omega) hz).mono (by omega) (by intros;assumption)
    · exact hexhaust n a t ht hz hcap
  | succ fuel ih =>
    intro n u hu hcap
    rw [searchH]
    refine (htrial n u hu (by omega) (checkCost+3+((checkCost+12)*fuel+(checkCost+22)))
      (fun a=>if zeroOkH hi b a then pure (n,a) else searchH hi b pre right fuel (n+1)) Out (fun a t ht=>?_)).mono ?_ (by intros;assumption)
    · by_cases hz : zeroOkH hi b a=true
      · simp only [if_pos hz]
        exact (hfinish n a t ht (by omega) hz).mono (by omega) (by intros;assumption)
      · simp only [if_neg hz]
        obtain ⟨v,hsteps,hv⟩:=hretry n a t ht hz (by omega)
        exact TBSim.steps hsteps (ih (n+1) v hv (by omega))
    · simp only [Nat.mul_succ]
      omega

#print axioms loop_sim
end OuterNodeLoopControl
