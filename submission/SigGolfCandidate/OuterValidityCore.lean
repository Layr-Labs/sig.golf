import SigGolfCandidate.OuterRuntime
set_option debug.skipKernelTC false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace OuterValidityCore
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv

def sizes : Sizes:=⟨5184,21756,131072⟩
def layout : Layout:=⟨0x65A0,0x80,0xa0,0x80000,0x7000,0x10A0⟩
theorem layout_valid (im : Image) (hb : 655360≤dataBase im) : layoutValid layout sizes im := by
  norm_num [layoutValid,layoutBuffers,layout,sizes,buffersDisjoint,disjointBuffers]
  omega

theorem valid (im : Image) (hbytes : im.byteSize<MAX_IMAGE_BYTES) (hb : 655360≤dataBase im) :
    im.Valid sizes layout := ⟨hbytes,layout_valid im hb⟩
#print axioms layout_valid
#print axioms valid
end OuterValidityCore
