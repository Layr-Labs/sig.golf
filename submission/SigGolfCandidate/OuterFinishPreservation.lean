import SigGolfCandidate.OuterLayerRecovery
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterFinishPreservation
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (HashOutput Layer Digest height chainCount route)
open SigGolfCandidate.T3M.Search (ENC EOUT DIGITS NODE NOUT NBUF OutAt)
open ClaudeWCT.W9.T3M SigGolfCandidate.Research
open ClaudeWCT.W9.Machine.Expand
namespace Scatter
open ClaudeWCT.W9.Machine.Expand.SharedScatter
theorem clear_scatter_finish {im:Image} (hz:SharedZero.ClearCode im)
    (hc:∀k:Fin 9,CoordinateCode im k.val) (ha:CodeAt im (pcOf 46509) afterCode)
    (hf:CodeAt im (pcOf 47005) finishCode) (he:CodeAt im (pcOf 43071) endCode)
    (output:HashOutput) (witness:SharedForest.Witness) (b:SharedCodec.CBytes)
    (s:MachineState) (hp:s.pc=pcOf 46980) (hin:SharedCompact.ForestAt s b)
    (hforest:witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hplan:SharedScatter.PlanAt s) (hout:OutAt s 96 output)
    (hc3:s.getMem 1184=(witness.counters 3).setWidth 64)
    (htail:∀ (j:Nat),1012≤j → j<2905 → j≠2789 → s.getMem (BitVec.ofNat 64 (2904+8*j))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*j))
    (hchoice:s.getMem (BitVec.ofNat 64 (2904+8*2789))=PostEnc.oldWord output (Paired.mainWitness witness) (8*2789))
    (hflag:s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0)) :
    ∃v,Steps im s 4984 5161 v ∧ v.pc=pcOf 49400 ∧ v.getReg .x5=1 ∧
      ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Phase1 output witness v ∧
      (∀ A, (0x66700 ≤ A ∧ A < 0x66760 ∨ 0x700000 ≤ A ∧ A < 0x700160 ∨ 0x7e1750 ≤ A ∧ A < 0x7e4c60 ∨
        0x7eb870 ≤ A ∧ A < 0x7f8000) → v.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨t,st,tp,tzero,tctr,tmode,tdigest,tr,tf⟩:=SharedZero.final_clear hz s hp
  have tin:SharedCompact.ForestAt t b:=hin.frame tf (by intros A hA hB hw;omega)
  have tplan:SharedScatter.PlanAt t:=hplan.frame tf (by intros A hA hB hw;omega)
  have tout:OutAt t NBUF output:=by
    intro k hk
    exact (tdigest k hk).trans (hout k hk)
  obtain ⟨v,tv,vp,v5,vfts,vold,vch,vf⟩:=scatter_finish_readout hc ha hf he output witness b t tp tin hforest
    (rawAt_of_output t output tout) tplan tmode (tctr.trans hc3)
    (by intro off hb hal;exact tzero _ (by omega) (by omega) (by omega)) (by
      intro j hj hbound hne
      exact (tf.get (by omega) (by omega)).trans (htail j hj hbound hne))
    ((tf.get (by omega) (by omega)).trans hchoice)
    ((tf.get (by decide) (by unfold Search.FLAG; omega)).trans hflag)
  refine ⟨v,st.trans tv,vp,v5,⟨vfts,vold,vch,?_⟩,?_⟩
  · have h0 : v.getMem (BitVec.ofNat 64 0x20160)=output.extractLsb' 0 64 := by
      rw [vf.get (by decide) (by unfold ScatterW; omega)]
      exact tout 0 (by decide)
    rw [h0]
    exact ClaudeWCT.W9.Machine.Expand.SharedCompactMain.leafOf_output output
  · intro A h
    rw [vf.get (by omega) (by unfold ScatterW; omega), tf.get (by omega) (by omega)]

#print axioms clear_scatter_finish
end Scatter
namespace Main
open ClaudeWCT.W9.Machine.Expand.SharedCompactMain
theorem finish_steps {im : Image} (hcompact : CompactCodeAt im)
    (hz : SharedZero.ClearCode im) (hc : ∀k:Fin 9,SharedScatter.CoordinateCode im k.val)
    (ha : CodeAt im (pcOf 46509) SharedScatter.afterCode)
    (hf : CodeAt im (pcOf 47005) SharedScatter.finishCode)
    (he : CodeAt im (pcOf 43071) SharedScatter.endCode)
    (hj : CodeAt im (pcOf 43761) [0x24c0306f])
    (output : HashOutput) (witness : SharedForest.Witness) (b : SharedCodec.CBytes)
    (s : MachineState) (hpc : s.pc=pcOf 41108)
    (hout : OutAt s 96 output) (hp : PlanAt s) (hlp : Compact2.LPlanAt s) (htp : Compact2.TopTabAt s)
    (hmain : ∀i,i<2873 → (i ≤ 4 ∨ 1161 ≤ i) → s.getMem (BitVec.ofNat 64 (2048+8*i))=
      (wordsOf (witListV5 output (Paired.mainWitness witness))).getD i 0)
    (hc3 : s.getMem 2080=(witness.counters 3).setWidth 64)
    (hin : SharedCompact.ForestAt s b)
    (hforest : witness.signature.forest=(SharedCodec.sigDecC b).forest)
    (hplan : SharedScatter.PlanAt s)
    (hflag : s.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0)) :
    ∃v,Steps im s 70972 71149 v ∧ v.pc=pcOf 49400 ∧ v.getReg .x5=1 ∧
      ClaudeWCT.W9.Machine.Expand.SharedCompactMain.Phase1 output witness v ∧
      (∀ A, (0x66700 ≤ A ∧ A < 0x66760 ∨ 0x700000 ≤ A ∧ A < 0x700160 ∨ 0x7e1750 ≤ A ∧ A < 0x7e4c60 ∨
        0x7eb870 ≤ A ∧ A < 0x7f8000) → v.getMem (BitVec.ofNat 64 A)=s.getMem (BitVec.ofNat 64 A)) := by
  obtain ⟨t,st,pt,main,ctr,keep⟩:=compact_main_steps hcompact output (Paired.mainWitness witness) s hpc hout hp hlp htp hmain
  have tin : SharedCompact.ForestAt t b := by
    intro k hk
    have old:=hin k hk
    exact ⟨(keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.1,
      (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans old.2⟩
  have tout : OutAt t 96 output := by
    intro k hk
    exact (keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)).trans (hout k hk)
  have tplan : SharedScatter.PlanAt t := by
    intro child j hj
    have hm:=Nat.mod_lt child.val (by decide : 0<32)
    have hh:=hplan child j hj
    rw [getByte_eq_word _ _ (by omega)] at hh ⊢
    rw [keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)]
    exact hh
  have ttail : ∀j,1012 ≤ j → j<2905 → j≠2789 → t.getMem (BitVec.ofNat 64 (2904+8*j))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*j) := by
    intro j hj hj' hne
    rw [main j hj hj',Compact2.wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq _ _) j hj']
    rfl
  have tchoice : t.getMem (BitVec.ofNat 64 (2904+8*2789))=
      PostEnc.oldWord output (Paired.mainWitness witness) (8*2789) := by
    rw [main 2789 (by norm_num) (by norm_num),
      Compact2.wordsOf_getD' _ 2905 (ClaudeWCT.W9.Machine.Expand.OldW.witList_length_eq _ _) 2789 (by norm_num)]
    rfl
  have tflag : t.getMem (BitVec.ofNat 64 Search.FLAG)=BitVec.ofNat 64 (if witness.topHigh then 128 else 0) :=
    (keep _ (by decide) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR Search.FLAG;omega)).trans hflag
  obtain ⟨imm,hd,ho⟩:=jalTo_sound (show jalTo (0x24c0306f#32) 43761=some 46980 by decide)
  have jump:=jal_x0_step hj hd ho t pt
  obtain ⟨v,tv,pv,v5,vph,vn⟩:=OuterFinishPreservation.Scatter.clear_scatter_finish hz hc ha hf he output witness b
    (t.setPC (pcOf 46980)) rfl tin hforest tplan tout (ctr.trans hc3) ttail tchoice tflag
  refine ⟨v,((st.trans jump).trans tv).of_eq (by norm_num) (by norm_num),pv,v5,vph,fun A h => ?_⟩
  rw [vn A h]
  exact keep _ (by omega) (by unfold Protected Compact.SNAP Compact2.SNAP2 Compact.InHold Compact2.Buffer.Post.SCR;omega)

#print axioms finish_steps
end Main
end OuterFinishPreservation
