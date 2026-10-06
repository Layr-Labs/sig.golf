import SigGolfCandidate.T3M.Verify.Nonbinary.InlineTailSteps

/- Actual retained twelve-word leaf setup on the unselected inline image.
   The final jump is retained and charged. This packet supplies actual fetch
   and ordinary execution; endpoint/hash-input/bank-HASH composition is separate. -/
namespace SigGolfCandidate.T3M.Nonbinary.InlineTail
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv
open SigGolfCandidate.T3M
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

def leafResult : Result := (symRun {} leafWords (pcOf 0) 13).getD
  ⟨SymState.init,.c 0,.endOfCode,0,0⟩

def leafCheck (rank : Nat) : Bool := rOK (run rank (leafPC rank) 13) leafResult &&
  decide (armPC rank ≤ leafPC rank ∧ leafPC rank-armPC rank ≤ (words rank).length)

theorem leaf_checks : ((List.range 64).all leafCheck)=true := by decide +kernel

theorem leaf_shape : leafResult.steps=12 ∧ leafResult.cycles=12 ∧ leafResult.stop=.jump := by
  decide +kernel

theorem leaf_run (rank : Nat) (hr : rank<64) :
    run rank (leafPC rank) 13=some leafResult := by
  have h:=List.all_eq_true.mp leaf_checks rank (List.mem_range.mpr hr)
  simp only [leafCheck,Bool.and_eq_true] at h
  exact rOK_eq h.1

theorem leaf_codeAt (rank : Nat) (hr : rank<64) :
    CodeAt image (pcOf (leafPC rank)) leafWords := by
  have h:=List.all_eq_true.mp leaf_checks rank (List.mem_range.mpr hr)
  simp only [leafCheck,Bool.and_eq_true] at h
  have hb:=of_decide_eq_true h.2
  have he:=of_decide_eq_true (List.all_eq_true.mp leaf_pc_check rank (List.mem_range.mpr hr))
  have hw:=of_decide_eq_true (List.all_eq_true.mp leaf_words_check rank (List.mem_range.mpr hr))
  rw [←he] at hw
  have hc:=window_codeAt rank (leafPC rank) hr hb.1 (by omega)
  rw [hw] at hc
  exact hc

theorem leaf_steps (rank : Nat) (hr : rank<64) (s : MachineState)
    (hpc : s.pc=pcOf (leafPC rank)) (hob : leafResult.obligs s) :
    Steps image s 12 12 (leafResult.toState s) := by
  have hc:=leaf_codeAt rank hr
  have hw:=of_decide_eq_true (List.all_eq_true.mp leaf_words_check rank (List.mem_range.mpr hr))
  have he:=of_decide_eq_true (List.all_eq_true.mp leaf_pc_check rank (List.mem_range.mpr hr))
  rw [←he] at hw
  have hrun:=leaf_run rank hr
  unfold run at hrun
  rw [hw] at hrun
  have hs:=symRun_sound hrun hc s hpc hob
  rw [leaf_shape.1,leaf_shape.2.1] at hs
  exact hs

#print axioms leaf_checks
#print axioms leaf_codeAt
#print axioms leaf_steps
end SigGolfCandidate.T3M.Nonbinary.InlineTail
