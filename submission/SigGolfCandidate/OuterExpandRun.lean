import SigGolfCandidate.OuterImageValidity
import SigGolfCandidate.OuterExpandMachine
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterExpandRun
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand
open SigGolfCandidate.T3 (HashOutput)
open OuterImageValidity OuterSignatureCodec
abbrev Result := HashOutput×SigGolfCandidate.Research.SharedForest.Witness×List Nat
def encode (r : Result) := OuterExpand.witEncOuter r.1 r.2.1 r.2.2

theorem work_lt : OuterExpandMachine.work+1<CYCLE_LIMIT := by decide +kernel

theorem initial (message : Message) (pk : PublicKey) (sig : NewSig) :
    initialState sub .expand (message,pk,sig)=some (w9init OuterImages.expandImage message pk sig) := by
  unfold initialState
  rw [if_pos OuterImageValidity.expand]
  simp only [inputBuffers,List.foldl_cons,List.foldl_nil]
  dsimp only [sub,OuterRuntime.runtimeSub,OuterImageValidity.images,w9init]

theorem halt {o : Option Result} {t : MachineState} (h : OuterForestHalt.Post o t) :
    fetch OuterImages.expandImage t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none=>exact ⟨h.2.2.2,h.2.1⟩
  | some p=>rcases p with ⟨output,w,ns⟩;exact ⟨h.2.2.2.2,h.2.1⟩

theorem readout {o : Option Result} {t : MachineState} (h : OuterForestHalt.Post o t) :
    o.map encode=if t.getReg .x10=0 then some (readOutput sub.sizes sub.layout .expand t) else none := by
  cases o with
  | none=>rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some p=>rcases p with ⟨output,w,ns⟩;rw [if_pos h.2.2.1];exact congrArg some h.2.2.2.1.symm

theorem refines (message : Message) (pk : PublicKey) (sig : NewSig) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> sub.run .expand (message,pk,sig)=
      (fun p=>(p.1.map encode,p.2.1,p.2.2)) <$>
        countBoth (mrealize 0 (OuterExpand.expandN message pk (SharedCodec.sigDecC (OuterSignatureCodec.expand sig)))) := by
  apply Sim.run_eq sub .expand (message,pk,sig) (initial message pk sig)
    (OuterExpandMachine.expand 0 message pk sig) (Nat.lt_of_succ_lt work_lt) (fun o=>o.map encode)
  intro o t h
  exact ⟨(halt h).1,(halt h).2,readout h⟩

theorem terminates (hash : Hash) (message : Message) (pk : PublicKey) (sig : NewSig) :
    (sub.runWith hash .expand (message,pk,sig)).finished=true ∧
      (sub.runWith hash .expand (message,pk,sig)).cycles<CYCLE_LIMIT := by
  obtain ⟨hf,hc⟩:=Sim.runWith sub .expand (message,pk,sig) (initial message pk sig)
    (OuterExpandMachine.expand 0 message pk sig) work_lt (fun _ _ h=>halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc work_lt⟩
#print axioms work_lt
#print axioms initial
#print axioms refines
#print axioms terminates
end OuterExpandRun
