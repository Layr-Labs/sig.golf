import SigGolfCandidate.T3M_Sign_Init
import SigGolfCandidate.T3M_Submission

namespace SigGolfCandidate.T3M.Sign
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
theorem dataBase_sign : dataBase (submission.image .sign) = SIGN_DATA := by
  unfold dataBase; rw [show (submission.image .sign).data.length = 86144 from Images.signData_length]; rfl
private theorem initialState_sign_generic (s : Submission) (sk : SecretKey)
    (cache : Bytes s.sizes.cache) (m : Message)
    (hv : (s.image .sign).Valid s.sizes s.layout) :
    initialState s .sign (sk, cache, m) = some
      (((((({ regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 } : MachineState).writeBytesAsWords
        (BitVec.ofNat 64 (dataBase (s.image .sign))) (s.image .sign).data).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.secretKey) (bytes sk)).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.cache) (bytes cache)).writeBytesAsWords
        (BitVec.ofNat 64 s.layout.message) (bytes m)).setReg .x2
        (BitVec.ofNat 64 (dataBase (s.image .sign)))) := by
  simp only [initialState, if_pos hv, inputBuffers, List.foldl_cons, List.foldl_nil]
theorem initialState_sign (sk : SecretKey) (cache : Bytes 131072) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (sinit sk cache m) := by
  rw [initialState_sign_generic submission sk cache m submission_sign_valid, dataBase_sign]
  rfl
end SigGolfCandidate.T3M.Sign
