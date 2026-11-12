import SigGolfCandidate.OuterForestCompactRecords
import SigGolfCandidate.OuterNoncePostMachine
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterNoncePostRecords
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine

def coord (i : Fin 5) : Fin 9 := ⟨[1,3,5,7,8].getD i.val 0,by fin_cases i <;> decide⟩
def destination (i : Fin 5) : Word := [11088,9392,7696,6000,5152].getD i.val 0

theorem record (s : MachineState) (ns : List Nat) (hr : OuterForestCompactRecords.Inv 9 ns s) (i : Fin 5) :
    s.getMem (BitVec.ofNat 64 (OuterSharedPost.record (coord i).val))=BitVec.ofNat 64 (ns.getD i.val 0) := by
  have h:=hr.record (coord i) (coord i).isLt (by fin_cases i <;> decide)
  have he : (coord i).val/2=i.val := by fin_cases i <;> decide
  simpa only [he] using h

theorem frame {P : Nat → Prop} {s t : MachineState} {ns : List Nat}
    (hr : OuterForestCompactRecords.Inv 9 ns s) (hf : Frame s t P)
    (hd : ∀ m : Fin 9,SharedV3.first m.val=false → ¬P (OuterSharedPost.record m.val)) :
    OuterForestCompactRecords.Inv 9 ns t := by
  refine ⟨hr.len,?_⟩
  intro m hm hfirst
  rw [hf _ (by unfold OuterSharedPost.record;omega) (hd m hfirst)]
  exact hr.record m hm hfirst

theorem result (s : MachineState) (ns : List Nat) (hr : OuterForestCompactRecords.Inv 9 ns s) :
    ∀ i : Fin 5,(OuterNoncePostMachine.postBlock.res.toState s).getMem (destination i)=BitVec.ofNat 64 (ns.getD i.val 0) := by
  intro i
  have H:=record s ns hr i
  fin_cases i
  all_goals
    simp only [coord,destination] at H ⊢
    first
    | exact OuterNoncePostMachine.nonce0 s |>.trans H
    | exact OuterNoncePostMachine.nonce1 s |>.trans H
    | exact OuterNoncePostMachine.nonce2 s |>.trans H
    | exact OuterNoncePostMachine.nonce3 s |>.trans H
    | exact OuterNoncePostMachine.nonce4 s |>.trans H

#print axioms result
end OuterNoncePostRecords
