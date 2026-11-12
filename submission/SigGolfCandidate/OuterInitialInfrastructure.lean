import SigGolfCandidate.OuterInitialMemoryEq
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterInitialInfrastructure
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3 (Digest)
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand ClaudeWCT.W9.Machine.Expand.SharedCompactMain

theorem initial_eq (m : Message) (pk : PublicKey) (b : SharedCodec.CBytes) :
    w9init OuterImages.expandImage m pk b=w9init Images.expandImage m pk b := by
  dsimp only [w9init,dataBase,OuterImages.expandImage,Images.expandImage]

#check initial_eq

theorem of_memory {b : SharedCodec.CBytes} {pk : Digest} {s t : MachineState}
    (hi : InitialMemory b pk s) (hm : s.getMem=t.getMem) : InitialMemory b pk t := by
  rcases s with ⟨sr,sm,sc,sp⟩
  rcases t with ⟨tr,tm,tc,tp⟩
  change sm=tm at hm
  subst tm
  refine ⟨hi.plan,hi.lplan,hi.toptab,hi.scatterPlan,hi.pk,hi.threshold1,hi.threshold2,hi.zt,hi.c32,?_,hi.table,hi.cf,hi.reward,hi.regionZero,hi.proj,hi.t51src⟩
  exact ⟨hi.zero.c0,hi.zero.c8,hi.zero.n32,hi.zero.n40,hi.zero.e40⟩

#check of_memory

theorem data_of_memory {s t : MachineState} (hd : SharedInit.DataAt s) (hm : s.getMem=t.getMem) :
    SharedInit.DataAt t := by
  intro i hi
  simpa only [MachineState.getByte,hm] using hd i hi

theorem initialized (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) (t : MachineState)
    (ht : PrePass.SigMemC t.getMem (OuterSignatureCodec.expand sig))
    (hf : ∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→t.getMem a=(w9init OuterImages.expandImage m pk sig).getMem a) :
    InitialMemory (OuterSignatureCodec.expand sig) pk t := by
  have hm:=OuterInitialMemoryEq.memory OuterImages.expandImage m pk sig t ht hf
  rw [initial_eq] at hm
  exact of_memory (initial_memory m pk _ (SharedCodec.fill_sigDecC _)) hm.symm
theorem initialized_data (m : Message) (pk : PublicKey) (sig : OuterSignatureCodec.NewSig) (t : MachineState)
    (ht : PrePass.SigMemC t.getMem (OuterSignatureCodec.expand sig))
    (hf : ∀ a,a∉(OuterCodecFrame.carrierWords++[33856])→t.getMem a=(w9init OuterImages.expandImage m pk sig).getMem a) :
    SharedInit.DataAt t := by
  have hm:=OuterInitialMemoryEq.memory OuterImages.expandImage m pk sig t ht hf
  rw [initial_eq] at hm
  exact data_of_memory (SharedInit.initial_data m pk _) hm.symm

#print axioms initialized_data
#print axioms initial_eq
#print axioms of_memory
#print axioms initialized
end OuterInitialInfrastructure
