import SigGolfCandidate.Cap776.TwentyChunk20
import SigGolfCandidate.Cap776.ForestInput
set_option debug.skipKernelTC true
namespace SigGolfResearch.Twenty
open Lean Elab Term
open Finset
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
attribute [local irreducible] ProbabilityRows.row SharedPathList.coordinate SharedPathPacked.product SharedPathPacked.addFirst

attribute [local irreducible] Count20_0 First20_0 Count20_1 First20_1 Count20_2 First20_2 Count20_3 First20_3 Count20_4 First20_4 Count20_5 First20_5 Count20_6 First20_6 Count20_7 First20_7 Count20_8 First20_8 Count20_9 First20_9 Count20_10 First20_10 Count20_11 First20_11 Count20_12 First20_12 Count20_13 First20_13 Count20_14 First20_14 Count20_15 First20_15 Count20_16 First20_16 Count20_17 First20_17 Count20_18 First20_18 Count20_19 First20_19 Count20_20 First20_20

noncomputable def countRow (t : Nat) : Nat :=
  match t with
  | 0 => Count20_0
  | 1 => Count20_1
  | 2 => Count20_2
  | 3 => Count20_3
  | 4 => Count20_4
  | 5 => Count20_5
  | 6 => Count20_6
  | 7 => Count20_7
  | 8 => Count20_8
  | 9 => Count20_9
  | 10 => Count20_10
  | 11 => Count20_11
  | 12 => Count20_12
  | 13 => Count20_13
  | 14 => Count20_14
  | 15 => Count20_15
  | 16 => Count20_16
  | 17 => Count20_17
  | 18 => Count20_18
  | 19 => Count20_19
  | 20 => Count20_20
  | _ => 0

theorem countRow_checked (t : Nat) (ht : t≤20) : row 20 t=countRow t := by
  rw [row_eq t ht]
  interval_cases t
  · exact count20_0
  · exact count20_1
  · exact count20_2
  · exact count20_3
  · exact count20_4
  · exact count20_5
  · exact count20_6
  · exact count20_7
  · exact count20_8
  · exact count20_9
  · exact count20_10
  · exact count20_11
  · exact count20_12
  · exact count20_13
  · exact count20_14
  · exact count20_15
  · exact count20_16
  · exact count20_17
  · exact count20_18
  · exact count20_19
  · exact count20_20
noncomputable def firstChunks (t : Nat) : Nat :=
  match t with
  | 0 => First20_0
  | 1 => First20_1
  | 2 => First20_2
  | 3 => First20_3
  | 4 => First20_4
  | 5 => First20_5
  | 6 => First20_6
  | 7 => First20_7
  | 8 => First20_8
  | 9 => First20_9
  | 10 => First20_10
  | 11 => First20_11
  | 12 => First20_12
  | 13 => First20_13
  | 14 => First20_14
  | 15 => First20_15
  | 16 => First20_16
  | 17 => First20_17
  | 18 => First20_18
  | 19 => First20_19
  | 20 => First20_20
  | _ => 0

theorem firstChunks_checked (t : Nat) (ht : t≤20) : pairChunkWith cache 20 t 1=firstChunks t := by
  interval_cases t
  · exact first20_0
  · exact first20_1
  · exact first20_2
  · exact first20_3
  · exact first20_4
  · exact first20_5
  · exact first20_6
  · exact first20_7
  · exact first20_8
  · exact first20_9
  · exact first20_10
  · exact first20_11
  · exact first20_12
  · exact first20_13
  · exact first20_14
  · exact first20_15
  · exact first20_16
  · exact first20_17
  · exact first20_18
  · exact first20_19
  · exact first20_20
elab "twenty_pair% " kind:num : term => do
  let mut total := 0
  for t in [:21] do
    let entryPrefix := if kind.getNat=0 then "Count20" else "First20"
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"{entryPrefix}_{t}")
    match limbValue? info.value! with
    | some n => total := total + (if kind.getNat=0 then Nat.choose 20 t*n else n)
    | none => throwError "invalid pair input"
  return limbExpr total

noncomputable def Pair20 : Nat := twenty_pair% 0
noncomputable def FirstPair20 : Nat := twenty_pair% 1

theorem pair20_checked : pairPacked 20=Pair20 :=
  (pair_of_rows 20 countRow countRow_checked).trans (by decide +kernel)

theorem first_pair20 : pairFirst 20=FirstPair20 := by
  have h := pairFirst_eq_cached_sum cache firstChunks 20 cache64_correct firstChunks_checked
  exact h.trans (by decide +kernel)

elab "twenty_forest% " kind:num : term => do
  let pname := if kind.getNat=0 then ``Pair20 else ``FirstPair20
  let info ← getConstInfo pname
  let coord ← getConstInfo ``Coordinate_128_20
  match limbValue? info.value!,limbValue? coord.value!.getAppArgs[if kind.getNat=0 then 2 else 3]! with
  | some p,some q => return limbExpr ((spreadFast 11 p)^4*spreadFast 10 q)
  | _,_ => throwError "invalid forest input"

noncomputable def CountForest20 : Nat := twenty_forest% 0
noncomputable def FirstForest20 : Nat := twenty_forest% 1

theorem countForest20 : ProbabilityRows.forestPacked 20=CountForest20 :=
  (forest_of_inputs 20 Pair20 Coordinate_128_20 pair20_checked coordinate_128_20_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

theorem firstForest20 : SharedPathPacked.forest 20=FirstForest20 :=
  (forest_eq_of_inputs 20 FirstPair20 Coordinate_128_20 first_pair20 coordinate_128_20_checked).trans
    (by rw [spread_eq_fast]; decide +kernel)

end SigGolfResearch.Twenty
