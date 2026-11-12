import SigGolfCandidate.OuterValidityCore
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option maxRecDepth 100000
namespace OuterValidityLengths
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

theorem valid (im : Image) (code : List (BitVec 32)) (data : List Byte)
    (hc : im.code=code) (hd : im.data=data) (n d : Nat) (hn : code.length=n) (hdata : data.length=d)
    (hbytes : 4*n+d<MAX_IMAGE_BYTES) (hbase : 655360≤16*((MEMORY_BYTES-d)/16)) :
    im.Valid OuterValidityCore.sizes OuterValidityCore.layout := by
  apply OuterValidityCore.valid im
  · simpa only [Image.byteSize,hc,hd,hn,hdata] using hbytes
  · simpa only [dataBase,hd,hdata] using hbase
#print axioms valid
end OuterValidityLengths
