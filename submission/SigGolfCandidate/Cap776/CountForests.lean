import SigGolfCandidate.Cap776.CountRow19
import SigGolfCandidate.Cap776.ForestInput
import SigGolfCandidate.Cap776.TwentyFinal
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open Lean Elab Term
open ClaudeWCT.Numerics ClaudeWCT.Numerics.SharedPathList ClaudeWCT.Numerics.SharedPathPacked
open ClaudeWCT.Numerics.SharedGeneratedCoordinate
open SigGolfResearch.ProbabilityRows
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
elab "prob_forest% " r:num : term => do
  let pinfo ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"Pair_{r.getNat}")
  let qname := if r.getNat=19 then ``Coordinate_128_19 else
    (s!"ClaudeWCT.Numerics.SharedGeneratedCoordinate.Coordinate_128_{r.getNat}").toName
  let qinfo ← getConstInfo qname
  match limbValue? pinfo.value!,limbValue? qinfo.value!.getAppArgs[2]! with
  | some p,some q => return limbExpr ((spreadFast 11 p)^4*spreadFast 10 q)
  | _,_ => throwError "invalid probability forest input"

noncomputable def CountForest_1 : Nat := prob_forest% 1
theorem countForest_1 : forestPacked 1=CountForest_1 :=
  (forest_of_inputs 1 Pair_1 Coordinate_128_1 pair_1_checked coordinate_128_1_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_2 : Nat := prob_forest% 2
theorem countForest_2 : forestPacked 2=CountForest_2 :=
  (forest_of_inputs 2 Pair_2 Coordinate_128_2 pair_2_checked coordinate_128_2_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_3 : Nat := prob_forest% 3
theorem countForest_3 : forestPacked 3=CountForest_3 :=
  (forest_of_inputs 3 Pair_3 Coordinate_128_3 pair_3_checked coordinate_128_3_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_4 : Nat := prob_forest% 4
theorem countForest_4 : forestPacked 4=CountForest_4 :=
  (forest_of_inputs 4 Pair_4 Coordinate_128_4 pair_4_checked coordinate_128_4_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_5 : Nat := prob_forest% 5
theorem countForest_5 : forestPacked 5=CountForest_5 :=
  (forest_of_inputs 5 Pair_5 Coordinate_128_5 pair_5_checked coordinate_128_5_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_6 : Nat := prob_forest% 6
theorem countForest_6 : forestPacked 6=CountForest_6 :=
  (forest_of_inputs 6 Pair_6 Coordinate_128_6 pair_6_checked coordinate_128_6_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_7 : Nat := prob_forest% 7
theorem countForest_7 : forestPacked 7=CountForest_7 :=
  (forest_of_inputs 7 Pair_7 Coordinate_128_7 pair_7_checked coordinate_128_7_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_8 : Nat := prob_forest% 8
theorem countForest_8 : forestPacked 8=CountForest_8 :=
  (forest_of_inputs 8 Pair_8 Coordinate_128_8 pair_8_checked coordinate_128_8_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_9 : Nat := prob_forest% 9
theorem countForest_9 : forestPacked 9=CountForest_9 :=
  (forest_of_inputs 9 Pair_9 Coordinate_128_9 pair_9_checked coordinate_128_9_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_10 : Nat := prob_forest% 10
theorem countForest_10 : forestPacked 10=CountForest_10 :=
  (forest_of_inputs 10 Pair_10 Coordinate_128_10 pair_10_checked coordinate_128_10_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_11 : Nat := prob_forest% 11
theorem countForest_11 : forestPacked 11=CountForest_11 :=
  (forest_of_inputs 11 Pair_11 Coordinate_128_11 pair_11_checked coordinate_128_11_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_12 : Nat := prob_forest% 12
theorem countForest_12 : forestPacked 12=CountForest_12 :=
  (forest_of_inputs 12 Pair_12 Coordinate_128_12 pair_12_checked coordinate_128_12_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_13 : Nat := prob_forest% 13
theorem countForest_13 : forestPacked 13=CountForest_13 :=
  (forest_of_inputs 13 Pair_13 Coordinate_128_13 pair_13_checked coordinate_128_13_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_14 : Nat := prob_forest% 14
theorem countForest_14 : forestPacked 14=CountForest_14 :=
  (forest_of_inputs 14 Pair_14 Coordinate_128_14 pair_14_checked coordinate_128_14_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_15 : Nat := prob_forest% 15
theorem countForest_15 : forestPacked 15=CountForest_15 :=
  (forest_of_inputs 15 Pair_15 Coordinate_128_15 pair_15_checked coordinate_128_15_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_16 : Nat := prob_forest% 16
theorem countForest_16 : forestPacked 16=CountForest_16 :=
  (forest_of_inputs 16 Pair_16 Coordinate_128_16 pair_16_checked coordinate_128_16_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_17 : Nat := prob_forest% 17
theorem countForest_17 : forestPacked 17=CountForest_17 :=
  (forest_of_inputs 17 Pair_17 Coordinate_128_17 pair_17_checked coordinate_128_17_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_18 : Nat := prob_forest% 18
theorem countForest_18 : forestPacked 18=CountForest_18 :=
  (forest_of_inputs 18 Pair_18 Coordinate_128_18 pair_18_checked coordinate_128_18_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def CountForest_19 : Nat := prob_forest% 19
theorem countForest_19 : forestPacked 19=CountForest_19 :=
  (forest_of_inputs 19 Pair_19 Coordinate_128_19 pair_19_checked coordinate_128_19_checked).trans
    (by rw [spread_eq_fast];decide +kernel)

noncomputable def countN (r : Nat) : Nat :=
  match r with
  | 1 => CountForest_1
  | 2 => CountForest_2
  | 3 => CountForest_3
  | 4 => CountForest_4
  | 5 => CountForest_5
  | 6 => CountForest_6
  | 7 => CountForest_7
  | 8 => CountForest_8
  | 9 => CountForest_9
  | 10 => CountForest_10
  | 11 => CountForest_11
  | 12 => CountForest_12
  | 13 => CountForest_13
  | 14 => CountForest_14
  | 15 => CountForest_15
  | 16 => CountForest_16
  | 17 => CountForest_17
  | 18 => CountForest_18
  | 19 => CountForest_19
  | 20 => SigGolfResearch.Twenty.CountForest20
  | _ => 0
theorem countN_eq (r : Nat) (h1 : 1≤r) (h19 : r≤20) : forestPacked r=countN r := by
  interval_cases r
  · exact countForest_1
  · exact countForest_2
  · exact countForest_3
  · exact countForest_4
  · exact countForest_5
  · exact countForest_6
  · exact countForest_7
  · exact countForest_8
  · exact countForest_9
  · exact countForest_10
  · exact countForest_11
  · exact countForest_12
  · exact countForest_13
  · exact countForest_14
  · exact countForest_15
  · exact countForest_16
  · exact countForest_17
  · exact countForest_18
  · exact countForest_19

  · exact SigGolfResearch.Twenty.countForest20

end SigGolfResearch.ProbabilityCache
