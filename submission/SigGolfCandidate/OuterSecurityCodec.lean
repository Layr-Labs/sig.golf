import SigGolfCandidate.OuterSecurityGame
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace OuterSecurityCodec
open OuterTailPacket OuterTailBytes OuterSignatureCodec
open ClaudeWCT.W9.T3M.SharedCodec

def decode (s : NewSig) : SigGolfCandidate.Research.SharedForest.Signature:=sigDecC (OuterSignatureCodec.expand s)

theorem clear_idem (v : Five) : clear (clear v)=clear v := by
  cases v
  apply Five.ext <;> simp [clear,BitVec.and_assoc]

theorem unpack_clear (v : Four) : clear (unpack v).1=(unpack v).1 := by
  have h:=congrArg Prod.fst (unpack_pack (unpack v).1 (unpack v).2)
  rw [pack_unpack] at h
  exact h.symm

theorem expand_clear (s : NewSig) :
    clear (read (splitOld (OuterSignatureCodec.expand s)).1)=read (splitOld (OuterSignatureCodec.expand s)).1 := by
  simp only [OuterSignatureCodec.expand,split_join,OuterTailBytes.expand,read_writeOld]
  exact unpack_clear _

theorem wire_decode (s : NewSig) : OuterSecurityGame.wire (decode s)=s := by
  unfold OuterSecurityGame.wire decode
  rw [sigBC_sigDecC,OuterSignatureCodec.compress_expand]

theorem signedWire_decode (s : NewSig) : OuterSecurityGame.signedWire (decode s)=s := by
  unfold OuterSecurityGame.signedWire decode
  rw [sigBC_sigDecC,OuterLooseCodec.compress_eq _ (expand_clear s),OuterSignatureCodec.compress_expand]
#print axioms wire_decode
#print axioms signedWire_decode
end OuterSecurityCodec
