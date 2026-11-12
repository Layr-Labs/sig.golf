import SigGolfCandidate.OuterImageValidity
import SigGolfCandidate.OuterSignInitial
import SigGolfCandidate.OuterSignBounds
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignRun
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open ClaudeWCT.W9.T3M.SharedCodec
open OuterImageValidity

theorem initial (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    initialState sub .sign (sk,cache,msg)=some (Sign.sinit sk cache msg) :=
  OuterSignInitial.initial rfl OuterImageValidity.sign sk cache msg

theorem refines (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (fun r=>(r.value,r.hashCalls,r.hashCompressions)) <$> sub.run .sign (sk,cache,msg)=
      (fun p=>(p.1.map (fun s=>OuterLooseCodec.compress (sigBC s)),p.2.1,p.2.2)) <$>
        countBoth (mrealize sk (OuterSigning.sign (cacheDec cache) msg)) :=
  OuterRuntime.refines rfl (Nat.lt_of_succ_lt OuterSignBounds.work_lt) _ sk cache msg
    (initial sk cache msg) (OuterSignMachine.sign sk cache msg)

theorem terminates (hash : Hash) (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    (sub.runWith hash .sign (sk,cache,msg)).finished=true ∧
      (sub.runWith hash .sign (sk,cache,msg)).cycles<CYCLE_LIMIT := by
  obtain ⟨hf,hc⟩:=Sim.runWith sub .sign (sk,cache,msg) (initial sk cache msg)
    (OuterSignMachine.sign sk cache msg) OuterSignBounds.work_lt (fun _ _ h=>OuterRuntime.halt h) hash
  exact ⟨hf,lt_of_le_of_lt hc OuterSignBounds.work_lt⟩
#print axioms initial
#print axioms refines
#print axioms terminates
end OuterSignRun
