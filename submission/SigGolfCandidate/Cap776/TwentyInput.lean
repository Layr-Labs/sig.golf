import SigGolfCandidate.Cap776.FirstForest19
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open Lean Elab Term
open ClaudeWCT.Numerics
open ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false

certify_coordinate 64 20 Coordinate_64_20 coordinate_64_20_checked
certify_coordinate 128 20 Coordinate_128_20 coordinate_128_20_checked

noncomputable def cache64 (r : Nat) : Cell :=
  if r≤19 then SigGolfResearch.ProbabilityCache.cache64 r else Coordinate_64_20
noncomputable def cache (_ r : Nat) : Cell := cache64 r

theorem cache64_correct (r : Nat) (hr : r≤20) : coordinate 64 r=cache64 r := by
  by_cases h : r≤19
  · simp only [cache64,if_pos h]
    exact SigGolfResearch.ProbabilityCache.cache64_correct r h
  · have he : r=20 := by omega
    subst r
    exact coordinate_64_20_checked

def rowFast (coord : Nat → Cell) (r t : Nat) : Nat :=
  let a := SharedPathPacked.product (coord t)
  let b := SharedPathPacked.product (coord (r-t))
  if t=0 then b.1 else if r-t=0 then a.1 else addFirstFast (a.1,a.1) (b.1,0)

theorem row_eq (t : Nat) (ht : t≤20) : row 20 t=rowFast cache64 20 t := by
  unfold row rowFast
  rw [cache64_correct t (by omega),cache64_correct (20-t) (by omega),addFirst_eq_fast]

elab "twenty_chunk% " kind:num t:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:21] do
    let name := if i=20 then ``Coordinate_64_20 else if i=19 then
      ``SigGolfResearch.ProbabilityCache.Coordinate_64_19 else
      (s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName
    let info ← getConstInfo name
    let args := info.value!.getAppArgs
    match limbValue? args[2]!,limbValue? args[3]! with
    | some x,some y => coordinates := coordinates.push (x,y)
    | _,_ => throwError "invalid coordinate numeral"
  let coord := fun i => coordinates[i]?.getD (0,0)
  let value := if kind.getNat=0 then rowFast coord 20 t.getNat
    else pairChunkWithFast (fun _ i => coord i) 20 t.getNat 1
  return limbExpr value
end SigGolfResearch.Twenty
