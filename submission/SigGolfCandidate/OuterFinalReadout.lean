import SigGolfCandidate.OuterWitnessNonceWords
import SigGolfCandidate.OuterNoncePostRecords
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterFinalReadout
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired
open ClaudeWCT.W9.Machine.Expand
open OuterExpand

theorem destination : ∀ k : Fin 5,OuterNoncePostRecords.destination k=BitVec.ofNat 64 (4256+outerNoncePos k.val) := by decide +kernel
theorem aligned : ∀ k : Fin 5,outerNoncePos k.val%8=0 := by decide +kernel

theorem mem_destination (X : Word) : X∈OuterNoncePostMachine.destinations ↔ ∃ k : Fin 5,X=OuterNoncePostRecords.destination k := by
  rw [show OuterNoncePostMachine.destinations=List.ofFn OuterNoncePostRecords.destination from rfl,List.mem_ofFn]
  constructor
  · rintro ⟨k,h⟩
    exact ⟨k,h.symm⟩
  · rintro ⟨k,h⟩
    exact ⟨k,h.symm⟩

theorem words (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (s t : MachineState)
    (hbuf : ∀ i,i<2720 → s.getMem (BitVec.ofNat 64 (4256+8*i))=(witEncF16 output w).extractLsb' (64*i) 64)
    (hout : ∀ k : Fin 5,t.getMem (OuterNoncePostRecords.destination k)=BitVec.ofNat 64 (ns.getD k.val 0))
    (hkeep : ∀ X,X∉OuterNoncePostMachine.destinations → t.getMem X=s.getMem X) :
    ∀ i,i<2720 → t.getMem (BitVec.ofNat 64 (4256+8*i))=(witEncOuter output w ns).extractLsb' (64*i) 64 := by
  classical
  intro i hi
  by_cases hit : ∃ k : Fin 5,8*i=outerNoncePos k.val
  · obtain ⟨k,hk⟩:=hit
    have ha : BitVec.ofNat 64 (4256+8*i)=OuterNoncePostRecords.destination k := by rw [destination,hk]
    rw [ha,hout,show 64*i=8*outerNoncePos k.val from by omega,OuterWitnessNonceWords.word]
  · have hnot : BitVec.ofNat 64 (4256+8*i)∉OuterNoncePostMachine.destinations := by
      rw [mem_destination]
      rintro ⟨k,hk⟩
      rw [destination] at hk
      have he:=congrArg BitVec.toNat hk
      have hp:=OuterWitnessNonceWords.pos_bounds k
      simp only [BitVec.toNat_ofNat] at he
      rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at he
      exact hit ⟨k,by omega⟩
    have hf:=OuterWitnessFreePadded.extract output w ns (8*i) 8 (by
      intro c hc
      have hn : 8*i≠outerNoncePos c := by intro h;exact hit ⟨⟨c,hc⟩,h⟩
      have hm:=aligned ⟨c,hc⟩
      dsimp only at hm
      omega)
    rw [show 8*(8*i)=64*i from by omega] at hf
    rw [hkeep _ hnot,hbuf i hi]
    exact hf.symm

theorem buffer (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (s t : MachineState)
    (hbuf : ∀ i,i<2720 → s.getMem (BitVec.ofNat 64 (4256+8*i))=(witEncF16 output w).extractLsb' (64*i) 64)
    (hout : ∀ k : Fin 5,t.getMem (OuterNoncePostRecords.destination k)=BitVec.ofNat 64 (ns.getD k.val 0))
    (hkeep : ∀ X,X∉OuterNoncePostMachine.destinations → t.getMem X=s.getMem X) :
    readBuffer t 4256 21756=witEncOuter output w ns :=
  ClaudeWCT.W9.Machine.Expand.SharedWitnessOutput.readBuffer_words t 4256 21756 2720 _ (by decide) (by decide) (by decide) (words output w ns s t hbuf hout hkeep)

#print axioms words
#print axioms buffer
end OuterFinalReadout
