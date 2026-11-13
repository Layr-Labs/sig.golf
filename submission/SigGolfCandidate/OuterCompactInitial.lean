import SigGolfCandidate.OuterCodecInput
import SigGolfCandidate.OuterImages
import SigGolfCandidate.Merge094
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterCompactInitial
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv
open SigGolfCandidate.T3M OuterCodecMachine OuterSignatureCodec
open ClaudeWCT.W9.T3M ClaudeWCT.W9.Machine.Expand
open ClaudeWCT.W9.Machine.Expand.PrePass

theorem input_words (im : Image) (m : Message) (pk : PublicKey) (sig : NewSig) :
    ∀ i,i<648→(w9init im m pk sig).getMem (BitVec.ofNat 64 (28672+8*i))=sig.extractLsb' (64*i) 64 := by
  intro i hi
  rw [w9_getMem im m pk (by decide : 5183≤5248) sig _ (by omega),if_pos (by omega),
    show 28672+8*i-28672=8*i by omega]
  exact SigGolfCandidate.T3M.Expand.bytesToWordLE_bytes_p sig i (by omega)

theorem tail_zero (im : Image) (hlen : im.data.length=29936) (m : Message) (pk : PublicKey) (sig : NewSig) :
    (w9init im m pk sig).getMem 33856=0 := by
  rw [show (33856 : Word)=BitVec.ofNat 64 33856 from rfl,
    w9_getMem im m pk (by decide : 5183≤5248) sig _ (by decide),if_neg (by decide)]
  unfold preSig
  rw [getMem_writeBytesAsWords _ _ 0xA0 33856 (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]) (by decide),if_neg (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]),
    getMem_writeBytesAsWords _ _ 0x65A0 33856 (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]) (by decide),if_neg (by simp [SigGolfCandidate.T3M.Expand.bytes_length_e]),
    ClaudeWCT.W9.Machine.Expand.SharedInit.dataBase_of_length hlen,
    getMem_writeBytesAsWords _ _ _ 33856 (by rw [hlen];decide) (by decide),if_neg (by simp [ClaudeWCT.W9.Machine.Expand.SharedInit.DB0])]
  rfl

theorem inflated (im : Image) (hlen : im.data.length=29936) (m : Message) (pk : PublicKey) (sig : NewSig) :
    SigMemC (unpackBlock.res.toState (w9init im m pk sig)).getMem (OuterSignatureCodec.expand sig) :=
  ⟨OuterCodecInput.words sig _ (input_words im m pk sig) (tail_zero im hlen m pk sig)⟩
#print axioms input_words
#print axioms tail_zero
#print axioms inflated
end OuterCompactInitial
