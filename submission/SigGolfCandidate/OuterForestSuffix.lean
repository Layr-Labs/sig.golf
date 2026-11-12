import SigGolfCandidate.OuterPlainForest
import SigGolfCandidate.OuterForestMemory
import SigGolfCandidate.OuterForestInitial
import SigGolfCandidate.OuterSuffix
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestSuffix
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Digest M)
open SigGolfCandidate.Research ClaudeWCT ClaudeWCT.W9.T3M
open ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

def appendNonces (ns : List Nat) : Option (HashOutput×SharedForest.Witness) → Option (HashOutput×SharedForest.Witness×List Nat)
  | none=>none
  | some (output,w)=>some (output,w,ns)

def SuffixDone : Option (HashOutput×SharedForest.Witness×List Nat) → MachineState → Prop
  | none,s=>OuterLayersRecovery.SuffixDone [] none s
  | some (output,w,ns),s=>OuterLayersRecovery.SuffixDone ns (some (output,w)) s

def forestProgram (output : HashOutput) (b : SharedCodec.CBytes) (counter : BitVec 32) (pk : Digest) :
    M (Option (HashOutput×SharedForest.Witness×List Nat)) := do
  let pair←OuterForestCorrectness.recoverForest (WCT9.digestIndex output) (SharedForest.forestSelectionFromOutput output)
    (SharedForest.forestWordsFromOutput output) (SharedCodec.sigDecC b).forest
  let result←OuterLayersRecovery.recoverProgram output (SharedCodec.sigDecC b) counter pair.1 pair.2.1 pair.2.2.1 pk
  pure (appendNonces pair.2.2.2 result)

def work : Nat := OuterForestRun.forestW+3821602689

theorem forest_suffix_good {sk : BitVec 256} {output : HashOutput} {b : SharedCodec.CBytes}
    {counter : BitVec 32} {pk : Digest} {s : MachineState}
    (hi : WCT9.digestIndex output<2^31) (hm : ForestMemory output b counter pk s)
    (hI : OuterForestInv.Inv (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)
      (WCT9.digestIndex output) (SharedForest.rawChildFromOutput output)
      (fun k=>SharedForest.forestRank output k.val) s 0
      (W9Machine.SharedV3.initialPair (Paired.witEnc output ⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩)) s) :
    TBSim OuterImages.expandImage sk s work (forestProgram output b counter pk) SuffixDone := by
  let w0 : SharedForest.Witness:=⟨SharedCompactMain.forestSig (SharedCodec.sigDecC b),counter,fun _=>0,false,[],fun _=>[],[],[]⟩
  have call:=OuterInstalledForest.run sk (Paired.witEnc output w0) (WCT9.digestIndex output) hi _ _ s hI
  rw [OuterPlainForest.forest output w0 _ hi] at call
  unfold forestProgram
  refine TBSim.bind (W₂:=3821602689) call (fun pair t ht=>?_)
  obtain ⟨tp,left,right,frame,fields,x8,recs,recs16,outer⟩:=ht
  have memory:=OuterForestMemory.memory_frame hm frame
  obtain ⟨u,tu,up,u2,u5,roots,rho,dc,zeros,moved,regs,fr⟩:=SharedHandoff.steps (SharedHandoff.code_of_driver OuterTopCodes.driver) t tp x8
  have uouter : OuterForestCompactRecords.Inv 9 pair.2.2.2 u := OuterNoncePostRecords.frame outer fr (by
    intro m _
    simp only [SharedHandoff.Writes,OuterSharedPost.record]
    have:=m.isLt
    omega)
  have ready:=handoff_ready memory hi up u5 left right roots rho dc zeros moved fr (ftsRecs_of_recInv recs) (ftsRecs16_of_recInv16 recs16)
  have H:=OuterLayersRecovery.layers_good (sk:=sk) pair.2.2.2 uouter ready
  have HM : TBSim OuterImages.expandImage sk u (3821600084+0)
      (OuterLayersRecovery.recoverProgram output (SharedCodec.sigDecC b) counter pair.1 pair.2.1 pair.2.2.1 pk >>=fun result=>pure (appendNonces pair.2.2.2 result)) SuffixDone := by
    refine TBSim.bind H ?_
    intro result v hres
    apply TBSim.pure
    cases result with
    | none=>exact hres
    | some p=>rcases p with ⟨out,w⟩;exact hres
  exact TBSim.steps tu HM

#print axioms forest_suffix_good
end OuterForestSuffix
