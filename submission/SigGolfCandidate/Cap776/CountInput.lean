import SigGolfCandidate.Cap776.ProbabilityBase
set_option debug.skipKernelTC false
namespace SigGolfResearch.ProbabilityCache
open Lean Elab Term
open ClaudeWCT.Numerics
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
attribute [local irreducible] ProbabilityRows.row SharedPathList.coordinate SharedPathPacked.product SharedPathPacked.addFirst
def rowFast (coord : Nat → Cell) (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coord t)
  let b := SharedPathPacked.product (coord (r-t))
  if t=0 then b.1 else if r-t=0 then a.1 else addFirstFast (a.1,a.1) (b.1,0)

theorem row_eq (r t : Nat) (hr : r≤19) (ht : t≤r) :
    row r t=rowFast cache64 r t := by
  unfold row rowFast
  rw [cache64_correct t (by omega),cache64_correct (r-t) (by omega),addFirst_eq_fast]

elab "prob_row% " r:num t:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:r.getNat+1] do
    let name := if i=19 then ``Coordinate_64_19 else
      (s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName
    let info ← getConstInfo name
    let args := info.value!.getAppArgs
    match limbValue? args[2]!, limbValue? args[3]! with
    | some x,some y => coordinates := coordinates.push (x,y)
    | _,_ => throwError "invalid coordinate numeral"
  return limbExpr (rowFast (fun i => coordinates[i]?.getD (0,0)) r.getNat t.getNat)

elab "prob_pair% " r:num : term => do
  let mut total := 0
  for t in [:r.getNat+1] do
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"Count_{r.getNat}_{t}")
    match limbValue? info.value! with
    | some n => total := total + Nat.choose r.getNat t*n
    | none => throwError "invalid count numeral"
  return limbExpr total

end SigGolfResearch.ProbabilityCache
