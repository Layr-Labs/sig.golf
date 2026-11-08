import SigGolfCandidate.Cap776.CountRow19
set_option debug.skipKernelTC false
namespace SigGolfResearch.ProbabilityCache
open Lean Elab Term
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def cache (_ r : Nat) : Cell := cache64 r
elab "first19% " t:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:20] do
    let name := if i=19 then ``Coordinate_64_19 else
      (s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName
    let info ← getConstInfo name
    let args := info.value!.getAppArgs
    match limbValue? args[2]!, limbValue? args[3]! with
    | some x,some y => coordinates := coordinates.push (x,y)
    | _,_ => throwError "invalid coordinate numeral"
  return limbExpr (pairChunkWithFast (fun _ i => coordinates[i]?.getD (0,0)) 19 t.getNat 1)


end SigGolfResearch.ProbabilityCache
