import SigGolfCandidate.OuterTopCodes
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterFrontMemory
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest)
open SigGolfCandidate.T3M.Search (NBUF OutAt)
open ClaudeWCT
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain
theorem cleared_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<12288)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226) :
    ∃t,Steps OuterImages.expandImage s 3740 3740 t ∧ t.pc=pcOf 45257 ∧
      (∀ (off:Nat),off+8≤8160 → off%8=0 → t.getMem (BitVec.ofNat 64 (2904+off))=0) ∧
      t.getMem 417824=0 ∧ t.getMem 0x66010=BitVec.ofNat 64 (WCT9.digestIndex output) ∧
      OutAt t NBUF output ∧ ForestMemory output b counter pk t := by
  have jump:=ClaudeWCT.W9.Machine.Sign.SharedDigestBoundary.expand_steps (SharedDigestCode.success_of_driver OuterTopCodes.driver) s hp
  let u:=s.setPC (pcOf 45232)
  obtain ⟨t,ut,tp,zeros,mode,ctr,index,idx,digest,regs,frame⟩:=
    SharedZero.accepted_clear OuterTopCodes.zero u rfl h17
  have memory:ForestMemory output b counter pk t:=
    memory_after_clear initial hin hh hhmem hs hsetup hout (ctr.trans h19) idx digest frame
  refine ⟨t,jump.trans ut,tp,?_,mode,?_,?_,memory⟩
  · intro off hb ha;exact zeros (2904+off) (by omega) (by omega) (by omega)
  · rw[index]
    have ho:u.getMem (0x20160:Word)=output.extractLsb' 0 64:=hout 0 (by decide)
    rw[ho];exact Compact2.index_shr output
  · intro i hi
    exact (frame.get (by unfold NBUF;omega) (by simp only [ClearWrites,NBUF];omega)).trans (hout i hi)

theorem accepted_front {s0 s:MachineState} {output:HashOutput} {b:SharedCodec.CBytes}
    {counter:BitVec 32} {pk:Digest}
    (initial:InitialMemory b pk s0) (hin:SharedCompact.InflatedAt s b)
    (hh:(SharedCodec.sigDecC b).policyHints.toNat<12288)
    (hhmem:s.getMem 0x66000=BitVec.ofNat 64 (SharedCodec.sigDecC b).policyHints.toNat)
    (hs:Frame s0 s SharedFront.SearchWrites)
    (hsetup:∀A,A=0x59B0 ∨ A=0x59B8 ∨ A=0x59C0 ∨ A=0x59C8 → s.getMem (BitVec.ofNat 64 A)=0)
    (hout:OutAt s NBUF output) (h19:s.getReg .x19=BitVec.ofNat 64 counter.toNat)
    (h17:s.getReg .x17=0x20160) (hp:s.pc=pcOf 45226)
    (hrank:∀k:Fin 9,SharedForest.rawForestRank output k.val<563) :
    ∃t,Steps OuterImages.expandImage s 4996 5173 t ∧ ForestMemory output b counter pk t ∧
      SharedForestRun.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)
        (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
        (fun k=>SharedForest.forestRank output k.val) t 0
        (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)) t := by
  obtain ⟨u,su,up,uz,um,ui,uo,uf⟩:=cleared_front initial hin hh hhmem hs hsetup hout h19 h17 hp
  have fields:=SharedForestRun.fields_of_output u output (WCT9.digestIndex output) ui uo hrank
  obtain ⟨t,ut,ht,hframe⟩:=SharedScatter.scatter_forest_pre OuterTopCodes.coordinates OuterTopCodes.afterCode
    output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩ b (WCT9.digestIndex output) u up uf.inflated rfl
    fields uf.stable.scatterPlan um uz rfl (forestSig_top _)
  exact ⟨t,su.trans ut,uf.frame (hframe.mono (fun _ _ h => Or.inl h)),ht⟩
#print axioms cleared_front
#print axioms accepted_front
end OuterFrontMemory
