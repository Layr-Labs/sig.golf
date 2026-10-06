import SigGolfCandidate.W9Machine.WctImage

namespace W9Machine.Frozen
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem image_eq : image = SigGolfCandidate.T3M.Images.InlineNative.image := by
  unfold image codeChunks dataChunks
    SigGolfCandidate.T3M.Images.InlineNative.image
    SigGolfCandidate.T3M.Images.InlineNative.code
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

end W9Machine.Frozen
