import SigGolfCandidate.OuterSharedBRun
import SigGolfCandidate.OuterSharedCRun
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace OuterSharedBank
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.T3
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open W9Machine W9Drv SigGolfCandidate.FtsGrind
open ClaudeWCT.W9.Machine.Expand.SharedScatter (coordRegion)

structure Codes (im : Image) : Prop where
  copies : SharedBank.CopyCodes im
  bankA : ∀ j,j<128 → SharedAProof.ChildCodeAt im j
  bankB : ∀ j,j<128 → CodeAt im (pcOf (SharedBProof.childBase j)) (OuterNodeBankLayout.bWords j)
  bankC : ∀ j,j<128 → CodeAt im (pcOf (SharedCProof.childBase j)) (OuterNodeBankLayout.cWords j)

def cost (k : Fin 9) : Nat := SharedBank.costG k+77831

theorem first_program (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (k : Fin 9) (raw : Fin 128) (ends : List Digest)
    (hf : SharedV3.first k.val=true) :
    OuterChildModel.childProgram w index k raw ends=
      (fun r=>(r.1,r.2.1,r.2.2,0)) <$> SharedChild.childProgramG w index k raw ends := by
  unfold OuterChildModel.childProgram OuterChildModel.child SharedChild.childProgramG
  simp only [hf,if_true]

theorem run (L : W9Machine.Layout) (sk : BitVec 256) (k : Fin 9) (raw : Fin 128)
    (codes : Codes L.image) (hchild : L.childWord raw=SharedBank.copyWord k.val raw.val)
    (hbase : Chain.base L k=coordRegion k.val) (w : ClaudeWCT.W9.T3M.WBytes) (index : Nat) (hi : index<2^31)
    (ends : List Digest) (x : MachineState) (hx : SharedChild.Pre L w index k raw ends x) :
    TBSim L.image sk x (cost k) (OuterChildModel.childProgram w index k raw ends) (OuterSharedPost.Post L k raw x) := by
  have hk:=k.isLt
  have hlo : 1848≤Chain.base L k := by rw [hbase];exact (OuterCopyFlatB.base_bounds k).1
  have hB : Chain.base L k<2^14 := by rw [hbase];exact (OuterCopyFlatB.base_bounds k).2
  have hw : widthOf (Chain.base L k)=ftsWidth k.val := by rw [hbase];exact (OuterChildModel.widths k).1
  have hsel : SEL16≤Chain.base L k ↔ k.val<4 := by
    rw [hbase,OuterNodeControllerGeometry.actual_frame k]
    unfold OuterNodeBufferGeometry.frameBase V3.regionOffset SEL16
    omega
  have hpj:=SharedV3.physical_lt k.val raw.val raw.isLt
  cases hf : SharedV3.first k.val with
  | true=>
    have hn : k.val<8 ∧ k.val%2=0 := by simpa only [SharedV3.first,decide_eq_true_eq] using hf
    have hphys : SharedV3.physical k.val raw.val=raw.val := by
      simp only [SharedV3.physical,hf,SigGolfCandidate.Research.SharedForest.physicalChild,↓reduceIte]
    have he : L.childWord raw=SharedAProof.copyBase raw.val := by
      rw [hchild]
      unfold SharedBank.copyWord SharedAProof.copyBase SharedAProof.cSlot
      rw [if_pos hn]
    have H:=SharedAProof.sharedC_tbsim (sk:=sk) k raw hf he (codes.copies.copyA _ raw.isLt) (codes.bankA _ raw.isLt)
      codes.copies.search (codes.copies.trampA _ raw.isLt) codes.copies.search16
      (by rw [hphys];exact codes.copies.tramp16A _ raw.isLt) hlo hB hw hsel w index ends x hx
    rw [first_program w index k raw ends hf]
    have HH:=H.mono le_rfl (fun r t ht=>OuterSharedPost.of_first hf ht)
    have HM:=OuterNodeSourceSim.map_sim (fun r : Digest×Nat×Nat=>(r.1,r.2.1,r.2.2,0)) HH
    exact HM.mono (by
      have hb:=SharedBank.copy_cost_A raw
      unfold cost SharedBank.costG
      omega) (fun _ _ h=>h)
  | false=>
    have hn : ¬(k.val<8 ∧ k.val%2=0) := by simpa only [SharedV3.first,decide_eq_false_iff_not] using hf
    have hraw : 2*(SharedV3.physical k.val raw.val%64)+SharedV3.physical k.val raw.val/64=raw.val := by
      have h:=SigGolfCandidate.Research.SharedForest.raw_physical_child false raw.val raw.isLt
      simpa only [SigGolfCandidate.Research.SharedForest.rawChild,SharedV3.physical,hf,Bool.false_eq_true,↓reduceIte] using h
    by_cases hc : k.val=8
    · have he : L.childWord raw=SharedCProof.copyBase (SharedV3.physical k.val raw.val) := by
        rw [hchild]
        unfold SharedBank.copyWord SharedCProof.copyBase SharedCProof.cSlot
        rw [if_neg hn,if_pos hc,hraw]
      have H:=OuterSharedCRun.run (sk:=sk) k raw index hf hc hi he (codes.copies.copyC _ hpj) (codes.bankC _ hpj)
        codes.copies.search (codes.copies.trampC _ hpj) codes.copies.search16 (codes.copies.tramp16C _ hpj) hbase w ends x hx
      refine H.mono ?_ (fun _ _ h=>h)
      have hb:=SharedBank.copy_cost_C ⟨_,hpj⟩
      dsimp only at hb
      unfold OuterCopyChildC.W cost SharedBank.costG
      rw [(OuterChildModel.widths k).1,(OuterChildModel.widths k).2]
      omega
    · have he : L.childWord raw=SharedBProof.copyBase (SharedV3.physical k.val raw.val) := by
        rw [hchild]
        unfold SharedBank.copyWord SharedBProof.copyBase SharedBProof.cSlot
        rw [if_neg hn,if_neg hc,hraw]
      have H:=OuterSharedBRun.run (sk:=sk) k raw index hf hc hi he (codes.copies.copyB _ hpj) (codes.bankB _ hpj)
        codes.copies.search (codes.copies.trampB _ hpj) codes.copies.search16 (codes.copies.tramp16B _ hpj) hbase w ends x hx
      refine H.mono ?_ (fun _ _ h=>h)
      have hb:=SharedBank.copy_cost_B ⟨_,hpj⟩
      dsimp only at hb
      unfold OuterCopyChildB.W cost SharedBank.costG
      rw [(OuterChildModel.widths k).1,(OuterChildModel.widths k).2]
      omega

#print axioms first_program
#print axioms run
end OuterSharedBank
