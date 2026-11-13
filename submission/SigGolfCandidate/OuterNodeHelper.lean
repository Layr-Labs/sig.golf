import SigGolfCandidate.OuterNodeSearchB
import SigGolfCandidate.OuterNodeSearchC
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodeHelper
open RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.FtsGrind OuterNodeSearchInvariant OuterNodeMachineBlocks

def bCode : List (BitVec 32) := b_saveCode++b_preHashCode++b_checkCode++b_failureCode++b_lastCode++b_postCode
def cCode : List (BitVec 32) := c_saveCode++c_preHashCode++c_checkCode++c_failureCode++c_lastCode++c_postCode

theorem pc_offset (b off : Nat) : pcOf (b+off)=pcOf b+BitVec.ofNat 64 (4*off) := by
  simp only [pcOf,Nat.mul_add,ofNat_add_ofNat,Nat.add_assoc]

theorem sizes : bCode.length=22 ∧ cCode.length=26 := by decide +kernel

theorem runB {im : Image} {sk : BitVec 256} {b A D : Nat} {pre right : List UInt8} {s : MachineState}
    (F : Input A D pre right s) (hc : CodeAt im (pcOf b) bCode) (hp : s.pc=pcOf b) :
    TBSim im sk s 61454 (searchH true 5 pre right 4095 0)
      (OuterNodeSearchExit.Out s A D (pcOf b-4#64)) := by
  have c0:=codeAt_sub (seg:=b_saveCode) 0 hc (by decide) (by rfl)
  have c4:=codeAt_sub (seg:=b_preHashCode) 4 hc (by decide) (by rfl)
  have c6:=codeAt_sub (seg:=b_checkCode) 6 hc (by decide) (by rfl)
  have c9:=codeAt_sub (seg:=b_failureCode) 9 hc (by decide) (by rfl)
  have c12:=codeAt_sub (seg:=b_lastCode) 12 hc (by decide) (by rfl)
  have c13:=codeAt_sub (seg:=b_postCode) 13 hc (by decide) (by rfl)
  obtain ⟨t,hs,ht⟩:=save F c0 hp
  have ht' : Stage s A D (pcOf (b+4)) 0 t := by
    simpa [pc_offset] using ht
  have h6 : CodeAt im (pcOf (b+4)+8#64) b_checkCode := by
    simpa [pc_offset,BitVec.add_assoc] using c6
  have h9 : CodeAt im (pcOf (b+4)+20#64) b_failureCode := by
    simpa [pc_offset,BitVec.add_assoc] using c9
  have h12 : CodeAt im (pcOf (b+4)+32#64) b_lastCode := by
    simpa [pc_offset,BitVec.add_assoc] using c12
  have h13 : CodeAt im (pcOf (b+4)+36#64) b_postCode := by
    simpa [pc_offset,BitVec.add_assoc] using c13
  have he:=OuterNodeSearchB.loop (sk:=sk) F c4 h6 h9 h12 h13 4095 0 t ht' (by decide)
  have he' : TBSim im sk t 61450 (searchH true 5 pre right 4095 0)
      (OuterNodeSearchExit.Out s A D (pcOf b-4#64)) := by
    simpa [pc_offset,BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps hs he'

theorem runC {im : Image} {sk : BitVec 256} {b A D : Nat} {pre right : List UInt8} {s : MachineState}
    (F : Input A D pre right s) (heap : Nat) (hheap : heap=2 ∨ heap=3)
    (hmem : s.getMem (BitVec.ofNat 64 (A+24))=BitVec.ofNat 64 heap) (hc : CodeAt im (pcOf b) cCode) (hp : s.pc=pcOf b) :
    TBSim im sk s 77838 (searchH (OuterNodeSearchC.high heap) 4 pre right 4095 0)
      (OuterNodeSearchExit.Out s A D (pcOf b-4#64)) := by
  have c0:=codeAt_sub (seg:=c_saveCode) 0 hc (by decide) (by rfl)
  have c4:=codeAt_sub (seg:=c_preHashCode) 4 hc (by decide) (by rfl)
  have c6:=codeAt_sub (seg:=c_checkCode) 6 hc (by decide) (by rfl)
  have c13:=codeAt_sub (seg:=c_failureCode) 13 hc (by decide) (by rfl)
  have c16:=codeAt_sub (seg:=c_lastCode) 16 hc (by decide) (by rfl)
  have c17:=codeAt_sub (seg:=c_postCode) 17 hc (by decide) (by rfl)
  obtain ⟨t,hs,ht⟩:=save F c0 hp
  have ht' : Stage s A D (pcOf (b+4)) 0 t := by
    simpa [pc_offset] using ht
  have h6 : CodeAt im (pcOf (b+4)+8#64) c_checkCode := by
    simpa [pc_offset,BitVec.add_assoc] using c6
  have h13 : CodeAt im (pcOf (b+4)+36#64) c_failureCode := by
    simpa [pc_offset,BitVec.add_assoc] using c13
  have h16 : CodeAt im (pcOf (b+4)+48#64) c_lastCode := by
    simpa [pc_offset,BitVec.add_assoc] using c16
  have h17 : CodeAt im (pcOf (b+4)+52#64) c_postCode := by
    simpa [pc_offset,BitVec.add_assoc] using c17
  have he:=OuterNodeSearchC.loop (sk:=sk) F heap hheap hmem c4 h6 h13 h16 h17 4095 0 t ht' (by decide)
  have he' : TBSim im sk t 77834 (searchH (OuterNodeSearchC.high heap) 4 pre right 4095 0)
      (OuterNodeSearchExit.Out s A D (pcOf b-4#64)) := by
    simpa [pc_offset,BitVec.sub_eq_add_neg,BitVec.add_assoc] using he
  exact TBSim.steps hs he'

#print axioms runB
#print axioms runC
end OuterNodeHelper
