import SigGolfCandidate.OuterNodeMachinePost
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodePostSplit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks
sym_block body := symRun {noAlias:=true} (b_postCode.take 6) (pcOf 246512) 40
sym_block tailB := symRun {noAlias:=true} (b_postCode.drop 6) (pcOf 246518) 40
sym_block tailC := symRun {noAlias:=true} (c_postCode.drop 6) (pcOf 235834) 40

theorem body_at (pc : Word) : symRun {noAlias:=true} (b_postCode.take 6) pc 40=
    some {body.res with pc:=.c (pc+24#64)} := by
  change some {body.res with pc:=.c (pc+4#64+4#64+4#64+4#64+4#64+4#64)} = _
  simp only [BitVec.add_assoc]
  rfl

theorem tailB_at (pc : Word) : symRun {noAlias:=true} (b_postCode.drop 6) pc 40=
    some {tailB.res with pc:=.c (pc-80#64)} := by
  change some {tailB.res with pc:=.c (pc+4#64+4#64+(-88#64))} = _
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

theorem tailC_at (pc : Word) : symRun {noAlias:=true} (c_postCode.drop 6) pc 40=
    some {tailC.res with pc:=.c (pc-96#64)} := by
  change some {tailC.res with pc:=.c (pc+4#64+4#64+(-104#64))} = _
  simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  rfl

#print axioms body_at
#print axioms tailB_at
#print axioms tailC_at
end OuterNodePostSplit
