import SigGolfCandidate.OuterRuntime
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterSignInitial
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.T3M
open SigGolfCandidate.T3M.Sign

theorem initial {imgs : Phase→Image} (hsign : imgs .sign=OuterImages.signImage)
    (hv : (imgs .sign).Valid (OuterRuntime.runtimeSub imgs).sizes (OuterRuntime.runtimeSub imgs).layout)
    (sk : SecretKey) (cache : Bytes 131072) (msg : SigGolfCandidate.T3.Message) :
    initialState (OuterRuntime.runtimeSub imgs) .sign (sk,cache,msg)=some (sinit sk cache msg) := by
  dsimp only [OuterRuntime.runtimeSub] at hv ⊢
  simp only [initialState,if_pos hv,inputBuffers,List.foldl_cons,List.foldl_nil]
  rw [hsign]
  have hd : dataBase OuterImages.signImage=SIGN_DATA:=by
    simp only [dataBase,OuterImages.signImage,Images.signData_length]
    rfl
  rw [hd]
  dsimp only [OuterImages.signImage,sinit,sdata]
#print axioms initial
end OuterSignInitial
