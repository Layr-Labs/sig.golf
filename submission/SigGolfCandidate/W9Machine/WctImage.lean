import SigGolfCandidate.T3M.Images.InlineNative

namespace W9Machine.Frozen
open SigGolfCandidate.T3M.Images

def codeChunks : List (List (BitVec 32)) := InlineNative.chunks
def dataChunks : List (List (BitVec 8)) := [InlineNative.image.data]
def image : SigGolfCandidate.Legacy.Riscv.Image := ⟨codeChunks.flatten, dataChunks.flatten⟩

end W9Machine.Frozen
