import SigGolfCandidate.OuterSignatureCodec
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLooseCodec
open OuterTailPacket OuterTailBytes OuterSignatureCodec

def packedWord (v : Five) (tail : BitVec 16) : BitVec 32 :=
  v.a.setWidth 32 ||| (v.b.setWidth 32 <<< 3) ||| (v.c.setWidth 32 <<< 6) |||
  (v.d.setWidth 32 <<< 9) ||| (v.e.setWidth 32 <<< 12) ||| (tail.setWidth 32 <<< 16)
def pack (v : Five) (tail : BitVec 16) : Four :=
  let w := packedWord v tail
  ⟨w.extractLsb' 0 8,w.extractLsb' 8 8,w.extractLsb' 16 8,w.extractLsb' 24 8⟩

theorem pack_eq (v : Five) (tail : BitVec 16) (h : clear v=v) : pack v tail=OuterTailPacket.pack v tail := by
  have ha:=congrArg Five.a h
  have hb:=congrArg Five.b h
  have hc:=congrArg Five.c h
  have hd:=congrArg Five.d h
  have he:=congrArg Five.e h
  change v.a &&& 7 = v.a at ha
  change v.b &&& 7 = v.b at hb
  change v.c &&& 7 = v.c at hc
  change v.d &&& 7 = v.d at hd
  change v.e &&& 15 = v.e at he
  simp only [pack,packedWord,OuterTailPacket.pack,OuterTailPacket.packedWord,ha,hb,hc,hd,he]

def compress (v : OldSig) : NewSig :=
  ofBytes 5183 (write (splitOld v).1 (pack (read (splitOld v).1) (splitOld v).2))

theorem compress_eq (v : OldSig) (h : clear (read (splitOld v).1)=read (splitOld v).1) :
    compress v=OuterSignatureCodec.compress v := by
  unfold compress OuterSignatureCodec.compress OuterTailBytes.compress
  rw [pack_eq _ _ h]

theorem roundtrip (v : OldSig) (h : clear (read (splitOld v).1)=read (splitOld v).1) :
    OuterSignatureCodec.expand (compress v)=v := by
  rw [compress_eq v h]
  exact OuterSignatureCodec.expand_compress v h
#print axioms pack_eq
#print axioms compress_eq
#print axioms roundtrip
end OuterLooseCodec
