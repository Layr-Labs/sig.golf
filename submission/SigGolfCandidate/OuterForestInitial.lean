import SigGolfCandidate.OuterInstalledForest
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterForestInitial
open OracleComp RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M W9Machine
open ClaudeWCT.W9.Machine.Expand

theorem of_old {w : W9Machine.WBytes} {index : Nat} {raw : Fin 9 → Fin 128} {ranks : Fin 9 → Fin 563}
    {initial u : MachineState} {n : Nat} {prev : SigGolfCandidate.T3.Digest×SigGolfCandidate.T3.Digest}
    (h : SharedForestRun.Inv w index raw ranks initial n prev u) :
    OuterForestInv.Inv w index raw ranks initial n prev u :=
  ⟨h.le,h.pc,h.fields,h.prevL,h.prevR,h.coords,h.frame.mono (fun _ _ hw=>Or.inl hw),h.x8⟩

theorem initial (w : W9Machine.WBytes) (index : Nat) (raw : Fin 9 → Fin 128) (ranks : Fin 9 → Fin 563) (s : MachineState)
    (hp : s.pc=pcOf 46513) (hf : SharedForestRun.Fields index raw ranks s)
    (hw : ∀ A,2904≤A → A+8≤10616 → A%8=0 → A≠2928 → W9Machine.OrigWD 1352 w s A) :
    OuterForestInv.Inv w index raw ranks s 0 (SharedV3.initialPair w) s :=
  of_old (SharedForestRun.initial_of_original w index raw ranks s hp hf hw)

#print axioms initial
end OuterForestInitial
