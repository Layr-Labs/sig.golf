import SigGolfCandidate.OuterSignCompleted
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterRuntime
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.Research.SharedForest ClaudeWCT.W9.T3M.SharedCodec

def runtimeSub (imgs : Phase→Image) : Submission :=
  ⟨⟨5184,21756,131072⟩,⟨0x65A0,0x80,0xa0,0x80000,0x7000,0x10A0⟩,imgs⟩

theorem halt {o : Option SharedSignature} {t : MachineState}
    (h : OuterSignCompleted.FinalPost o t) : fetch OuterImages.signImage t=some (.base .ECALL) ∧ t.getReg .x5=1 := by
  cases o with
  | none=>exact ⟨h.2.2.2,h.2.1⟩
  | some sig=>exact ⟨h.2.2.2.2,h.2.1⟩

theorem readout {imgs : Phase→Image} {o : Option SharedSignature} {t : MachineState}
    (h : OuterSignCompleted.FinalPost o t) :
    o.map (fun s=>OuterLooseCodec.compress (sigBC s))=if t.getReg .x10=0 then
      some (readOutput (runtimeSub imgs).sizes (runtimeSub imgs).layout .sign t) else none := by
  cases o with
  | none=>rw [if_neg (by rw [h.2.2.1];decide)];rfl
  | some sig=>rw [if_pos h.2.2.1];exact congrArg some h.2.2.2.1.symm

theorem refines {imgs : Phase→Image} (hsign : imgs .sign=OuterImages.signImage) {W : Nat}
    (hW : W<CYCLE_LIMIT) (program : SigGolfCandidate.T3.M (Option SharedSignature))
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message)
    {s : MachineState} (hinit : initialState (runtimeSub imgs) .sign (sk,cache,msg)=some s)
    (hsim : TBSim OuterImages.signImage sk s W program OuterSignCompleted.FinalPost) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> (runtimeSub imgs).run .sign (sk,cache,msg)=
      (fun p=>(p.1.map (fun s=>OuterLooseCodec.compress (sigBC s)),p.2.1,p.2.2)) <$>
        countBoth (mrealize sk program) := by
  have ht : TBSim (imgs .sign) sk s W program OuterSignCompleted.FinalPost:=hsign.symm ▸ hsim
  apply Sim.run_eq (runtimeSub imgs) .sign (sk,cache,msg) hinit ht hW (fun o=>o.map (fun s=>OuterLooseCodec.compress (sigBC s)))
  intro o t h
  refine ⟨?_,(halt h).2,readout h⟩
  change fetch (imgs .sign) t=some (.base .ECALL)
  rw [hsign]
  exact (halt h).1
#print axioms halt
#print axioms readout
#print axioms refines
end OuterRuntime
