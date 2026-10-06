import SigGolfCandidate.T3M.Sign.PackedLowTree
import SigGolfCandidate.ClaudeWCT.WCT9.Core

namespace SigGolfCandidate.T3M.Sign.Packed
open SigGolfCandidate.T3
open ClaudeWCT
def signLayersP (leafFn : LeafFn) (cache : Cache) (index : Nat) : Nat → WCT9.LayerMsg → M (Option (List Pieces))
  | 0, _ => pure (some [])
  | n + 1, msg => do
      let lay : Layer := Fin.ofNat 4 n
      let (leaf, tree) := route index lay
      let found ← WCT9.layerCounterSearch lay tree leaf msg 0 (WCT9.searchLimit lay)
      if n = 0 then
        let part ← signTop cache leaf ((found.map Prod.snd).getD dummyTop)
        pure (some [part])
      else
        let some (_, digits) := found | pure none
        let (levels, values) ← buildTreeP leafFn lay tree leaf digits
        let path := (List.range (height lay)).map fun j =>
          (levels.getD j []).getD (leaf / 2 ^ j ^^^ 1) 0
        let top := WCT9.topPair lay levels
        let some previous ← signLayersP leafFn cache index n (.pair top.1 top.2) | pure none
        pure (some (previous ++ [(values, path)]))
end SigGolfCandidate.T3M.Sign.Packed
