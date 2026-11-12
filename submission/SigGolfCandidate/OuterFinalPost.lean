import SigGolfCandidate.OuterFinalReadout
import SigGolfCandidate.OuterControlRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterFinalPost
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.T3M.Paired

def Post (ns : List Nat) : Option (HashOutput×SigGolfCandidate.Research.SharedForest.Witness) → MachineState → Prop
  | none,t=>(t.pc=pcOf 356 ∨ t.pc=pcOf 45231) ∧ t.getReg .x5=1 ∧ t.getReg .x10=1 ∧ fetch OuterImages.expandImage t=some (.base .ECALL)
  | some (output,w),t=>t.pc=pcOf 88280 ∧ t.getReg .x5=1 ∧ t.getReg .x10=0 ∧
      readBuffer t 4256 21756=OuterExpand.witEncOuter output w ns ∧ fetch OuterImages.expandImage t=some (.base .ECALL)

theorem run (s : MachineState) (output : HashOutput) (w : SigGolfCandidate.Research.SharedForest.Witness) (ns : List Nat)
    (hp : s.pc=pcOf 84218) (h5 : s.getReg .x5=1) (h10 : s.getReg .x10=0)
    (hr : OuterForestCompactRecords.Inv 9 ns s)
    (hbuf : ∀ i,i<2720 → s.getMem (BitVec.ofNat 64 (4256+8*i))=(witEncF16 output w).extractLsb' (64*i) 64) :
    ∃ t,Steps OuterImages.expandImage s 21 21 t ∧ Post ns (some (output,w)) t := by
  obtain ⟨t,ht,hpc,hfetch,hregs,h0,h1,h2,h3,h4,hframe⟩:=OuterControlRun.post s hp
  have hout (k : Fin 5) : t.getMem (OuterNoncePostRecords.destination k)=BitVec.ofNat 64 (ns.getD k.val 0) := by
    have H:=OuterNoncePostRecords.record s ns hr k
    fin_cases k
    all_goals first | exact h0.trans H | exact h1.trans H | exact h2.trans H | exact h3.trans H | exact h4.trans H
  refine ⟨t,ht,hpc,?_,?_,OuterFinalReadout.buffer output w ns s t hbuf hout hframe,hfetch⟩
  · rw [hregs .x5 (by decide),h5]
  · rw [hregs .x10 (by decide),h10]

#print axioms run
end OuterFinalPost
