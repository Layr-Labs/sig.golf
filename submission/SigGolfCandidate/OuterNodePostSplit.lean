import SigGolfCandidate.OuterNodeMachinePost
set_option debug.skipKernelTC false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
namespace OuterNodePostSplit
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterNodeMachineBlocks
sym_block body := symRun {noAlias:=true} (b_postCode.take 6) (pcOf 246512) 40
sym_block tailB := symRun {noAlias:=true} (b_postCode.drop 6) (pcOf 246518) 40

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

-- C47: the c8 grinder's exit block (8 words, no jump), split after the constant slot address (`lui t2,0x7fb` and
-- four `nop`s) so that the store runs on a symbolic `t2`.
sym_block cBody := symRun {noAlias:=true} (c_postCode.take 5) (pcOf 235828) 40
sym_block cTail := symRun {noAlias:=true} (c_postCode.drop 5) (pcOf 235833) 40
theorem cBody_at (pc : Word) : symRun {noAlias:=true} (c_postCode.take 5) pc 40=
    some {cBody.res with pc:=.c (pc+20#64)} := by
  change some {cBody.res with pc:=.c (pc+4#64+4#64+4#64+4#64+4#64)} = _
  simp only [BitVec.add_assoc]
  rfl
theorem cTail_at (pc : Word) : symRun {noAlias:=true} (c_postCode.drop 5) pc 40=
    some {cTail.res with pc:=.c (pc+12#64)} := by
  change some {cTail.res with pc:=.c (pc+4#64+4#64+4#64)} = _
  simp only [BitVec.add_assoc]
  rfl

#print axioms body_at
#print axioms tailB_at
#print axioms cBody_at
#print axioms cTail_at
end OuterNodePostSplit
