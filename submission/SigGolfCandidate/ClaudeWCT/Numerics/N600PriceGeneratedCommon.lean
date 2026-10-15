import SigGolfCandidate.ClaudeWCT.Numerics.N600PricePart4

set_option Elab.async false

namespace ClaudeWCT.Numerics.SharedGeneratedPair
open Lean Elab Command
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open ClaudeWCT.Numerics.SharedPathList (Cell coordinate)
open ClaudeWCT.Numerics.SharedPathPacked
set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000
set_option Elab.async false

noncomputable def cachedCoordinate (_ r : Nat) : Cell :=
  match r with
  | 0 => Coordinate_64_0
  | 1 => Coordinate_64_1
  | 2 => Coordinate_64_2
  | 3 => Coordinate_64_3
  | 4 => Coordinate_64_4
  | 5 => Coordinate_64_5
  | 6 => Coordinate_64_6
  | 7 => Coordinate_64_7
  | 8 => Coordinate_64_8
  | 9 => Coordinate_64_9
  | 10 => Coordinate_64_10
  | 11 => Coordinate_64_11
  | 12 => Coordinate_64_12
  | 13 => Coordinate_64_13
  | 14 => Coordinate_64_14
  | 15 => Coordinate_64_15
  | 16 => Coordinate_64_16
  | 17 => Coordinate_64_17
  | 18 => Coordinate_64_18
  | _ => (0,0)

theorem cachedCoordinate_correct (r : Nat) (hr : r ≤ 18) :
    ClaudeWCT.Numerics.SharedPathList.coordinate 64 r = cachedCoordinate 64 r := by
  interval_cases r
  · exact coordinate_64_0_checked
  · exact coordinate_64_1_checked
  · exact coordinate_64_2_checked
  · exact coordinate_64_3_checked
  · exact coordinate_64_4_checked
  · exact coordinate_64_5_checked
  · exact coordinate_64_6_checked
  · exact coordinate_64_7_checked
  · exact coordinate_64_8_checked
  · exact coordinate_64_9_checked
  · exact coordinate_64_10_checked
  · exact coordinate_64_11_checked
  · exact coordinate_64_12_checked
  · exact coordinate_64_13_checked
  · exact coordinate_64_14_checked
  · exact coordinate_64_15_checked
  · exact coordinate_64_16_checked
  · exact coordinate_64_17_checked
  · exact coordinate_64_18_checked

/- The elaborator only proposes a numeral. The following theorem checks the
entire arithmetic expression in the kernel, independently of that proposal. -/
elab "pair_chunk_numeral% " r:num start:num size:num : term => do
  let mut coordinates : Array Cell := #[]
  for i in [:19] do
    let info ← getConstInfo ((s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_64_{i}").toName)
    let args := info.value!.getAppArgs
    match args[2]!.nat?, args[3]!.nat? with
    | some x, some y => coordinates := coordinates.push (x,y)
    | _, _ => throwError "coordinate cache {i} is not a pair of Nat literals"
  let value := pairChunkWith (fun _ n => coordinates[n]?.getD (0,0))
    r.getNat start.getNat size.getNat
  return mkNatLit value

elab "certify_pair_chunk " r:num start:num size:num cached:ident proof:ident : command => do
  elabCommand (← `(noncomputable def $cached : Nat := pair_chunk_numeral% $r $start $size))
  elabCommand (← `(theorem $proof :
    pairChunkWith cachedCoordinate $r $start $size = $cached := by decide +kernel))

elab "pair_sum_numeral% " r:num : term => do
  let mut total := 0
  for i in [:r.getNat+1] do
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"Pair_{r.getNat}_{i}")
    match info.value!.nat? with
    | some n => total := total+n
    | none => throwError "pair chunk {i} is not a Nat literal"
  return mkNatLit total

end ClaudeWCT.Numerics.SharedGeneratedPair
namespace ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedPathList (Cell)
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem forest_eq_of_inputs (r p : Nat) (q : Cell)
    (hp : pairFirst r=p) (hq : ClaudeWCT.Numerics.SharedPathList.coordinate 128 r=q) :
    forest r=(spread 11 p)^4*spread 10 q.2 :=
  congrArg₂ (fun (x : Nat) (y : Cell) => (spread 11 x)^4*spread 10 y.2) hp hq

end ClaudeWCT.Numerics.SharedPathPacked

namespace ClaudeWCT.Numerics.SharedFees
open ClaudeWCT.Numerics.SharedMoments
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option Elab.async false

theorem convolutionDots_eq_of_fees (r p mass mgf res : Nat)
    (h0 : packedFee 0=mass) (h1 : packedFee 1=mgf) (h2 : packedFee 2=res) :
    convolutionDots r p =
      (packedDot p mgf + maxFee*(forestMoment r-packedDot p mass),
       packedDot p res + scale*(forestMoment r-packedDot p mass)) := by
  subst mass
  subst mgf
  subst res
  rfl

end ClaudeWCT.Numerics.SharedFees
