import SigGolfCandidate.ByteDispatchCore
import SigGolfCandidate.Merge112
set_option debug.skipKernelTC false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SigGolfCandidate.T3M.ByteDispatch
open SigGolfCandidate.Legacy SigGolfCandidate.Rv RiscvZkvm.Rv64 SigGolfCandidate.Legacy.Riscv
open SigGolfCandidate.T3M.Nonbinary in
 theorem writes_below_source (c : NCtx) (hc : c.ok) (i A : Nat) (hi : i≤51) (hA : 16136≤A) : ¬c.Wr i A := by
  have hb:=c.bufferEnd_bounds i
  have hs : slot i+16≤16136 := by unfold slot;split_ifs <;> omega
  have hh:=hc.2.2.2.2.1
  unfold NCtx.Wr
  rw [NCtx.slot0,NCtx.slot1]
  omega

open SigGolfCandidate.T3M.Nonbinary in
 theorem source_preserved (c : NCtx) (hc : c.ok) (i : Nat) (hi : i≤51)
    (s0 s : MachineState) (acc : List (BitVec 128)) (v : BitVec 128)
    (hs : Source v s0) (hB : c.Base s0 (c.Wr i) acc s) : Source v s := by
  obtain ⟨d,hd,ha,hb,hr,hv⟩:=hs
  have hmem0:=hB.2.1.get (A:=d) (by unfold MEMORY_BYTES at hb;omega)
    (writes_below_source c hc i d hi hd)
  have hmem8:=hB.2.1.get (A:=d+8) (by unfold MEMORY_BYTES at hb;omega)
    (writes_below_source c hc i (d+8) hi (by omega))
  refine ⟨d,hd,ha,hb,(hB.1 .x16 (by decide +kernel)).trans hr,?_,?_⟩
  · exact hmem0.trans hv.1
  · exact hmem8.trans hv.2


#print axioms writes_below_source
#print axioms source_preserved
end SigGolfCandidate.T3M.ByteDispatch
