import SigGolfCandidate.Cap776.FirstChunk19
set_option debug.skipKernelTC true
namespace SigGolfResearch.ProbabilityCache
open Lean Elab Term
open ClaudeWCT.Numerics.SharedPathPacked ClaudeWCT.Numerics.SharedGeneratedCoordinate
set_option maxHeartbeats 200000000
set_option maxRecDepth 1000000
set_option Elab.async false
noncomputable def chunks (t : Nat) : Nat :=
  match t with
  | 0 => First19_0
  | 1 => First19_1
  | 2 => First19_2
  | 3 => First19_3
  | 4 => First19_4
  | 5 => First19_5
  | 6 => First19_6
  | 7 => First19_7
  | 8 => First19_8
  | 9 => First19_9
  | 10 => First19_10
  | 11 => First19_11
  | 12 => First19_12
  | 13 => First19_13
  | 14 => First19_14
  | 15 => First19_15
  | 16 => First19_16
  | 17 => First19_17
  | 18 => First19_18
  | 19 => First19_19
  | _ => 0
theorem chunks_checked (t : Nat) (ht : t≤19) : pairChunkWith cache 19 t 1=chunks t := by
  interval_cases t
  · exact first19_0
  · exact first19_1
  · exact first19_2
  · exact first19_3
  · exact first19_4
  · exact first19_5
  · exact first19_6
  · exact first19_7
  · exact first19_8
  · exact first19_9
  · exact first19_10
  · exact first19_11
  · exact first19_12
  · exact first19_13
  · exact first19_14
  · exact first19_15
  · exact first19_16
  · exact first19_17
  · exact first19_18
  · exact first19_19
elab "first_pair19%" : term => do
  let mut total := 0
  for i in [:20] do
    let j := i
    let info ← getConstInfo ((← getCurrNamespace) ++ Name.mkSimple s!"First19_{j}")
    match limbValue? info.value! with
    | some n => total := total+n
    | none => throwError "invalid first moment numeral"
  return limbExpr total

noncomputable def FirstPair19 : Nat := first_pair19%

theorem first_pair19 : pairFirst 19=FirstPair19 := by
  have h := pairFirst_eq_cached_sum cache chunks 19 cache64_correct chunks_checked
  exact h.trans (by decide +kernel)

elab "first_forest19%" : term => do
  let info ← getConstInfo ``FirstPair19
  let coord ← getConstInfo ``Coordinate_128_19
  match limbValue? info.value!,limbValue? coord.value!.getAppArgs[3]! with
  | some p,some q => return limbExpr ((spreadFast 11 p)^4*spreadFast 10 q)
  | _,_ => throwError "invalid forest inputs"

noncomputable def FirstForest19 : Nat := first_forest19%

theorem first_forest19 : forest 19=FirstForest19 := by
  exact (forest_eq_of_inputs 19 FirstPair19 Coordinate_128_19
    first_pair19 coordinate_128_19_checked).trans (by rw [spread_eq_fast]; decide +kernel)

end SigGolfResearch.ProbabilityCache
