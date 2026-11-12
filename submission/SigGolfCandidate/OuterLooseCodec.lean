import SigGolfCandidate.OuterSignatureCodec
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace OuterLooseCodec
open OuterTailPacket OuterTailBytes OuterSignatureCodec

def pack (v : Five) (tail : BitVec 16) : Five :=
  ⟨v.a ||| ((tail.truncate 8 &&& 7) <<< 5),
   v.b ||| (((tail >>> 3).truncate 8 &&& 7) <<< 5),
   v.c ||| (((tail >>> 6).truncate 8 &&& 7) <<< 5),
   v.d ||| (((tail >>> 9).truncate 8 &&& 7) <<< 5),
   v.e ||| (((tail >>> 12).truncate 8 &&& 15) <<< 4)⟩

theorem pack_eq (v : Five) (tail : BitVec 16) (h : clear v=v) : pack v tail=OuterTailPacket.pack v tail := by
  have ha:=congrArg Five.a h
  have hb:=congrArg Five.b h
  have hc:=congrArg Five.c h
  have hd:=congrArg Five.d h
  have he:=congrArg Five.e h
  simp only [clear] at ha hb hc hd he
  change v.a &&& (↑(31 : Nat) : BitVec 8) = v.a at ha
  change v.b &&& (↑(31 : Nat) : BitVec 8) = v.b at hb
  change v.c &&& (↑(31 : Nat) : BitVec 8) = v.c at hc
  change v.d &&& (↑(31 : Nat) : BitVec 8) = v.d at hd
  change v.e &&& (↑(15 : Nat) : BitVec 8) = v.e at he
  simp only [pack,OuterTailPacket.pack,ha,hb,hc,hd,he]

def compress (v : OldSig) : NewSig :=
  ofBytes 5184 (write (splitOld v).1 (pack (read (splitOld v).1) (splitOld v).2))

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
