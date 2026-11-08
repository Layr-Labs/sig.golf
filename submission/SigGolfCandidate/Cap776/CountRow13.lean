import SigGolfCandidate.Cap776.CountRow12
import SigGolfCandidate.Cap776.ForestInput
set_option debug.skipKernelTC true
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
noncomputable def Count_13_0 : Nat := prob_row% 13 0
theorem count_13_0 : rowFast cache64 13 0=Count_13_0 := by decide +kernel
noncomputable def Count_13_1 : Nat := prob_row% 13 1
theorem count_13_1 : rowFast cache64 13 1=Count_13_1 := by decide +kernel
noncomputable def Count_13_2 : Nat := prob_row% 13 2
theorem count_13_2 : rowFast cache64 13 2=Count_13_2 := by decide +kernel
noncomputable def Count_13_3 : Nat := prob_row% 13 3
theorem count_13_3 : rowFast cache64 13 3=Count_13_3 := by decide +kernel
noncomputable def Count_13_4 : Nat := prob_row% 13 4
theorem count_13_4 : rowFast cache64 13 4=Count_13_4 := by decide +kernel
noncomputable def Count_13_5 : Nat := prob_row% 13 5
theorem count_13_5 : rowFast cache64 13 5=Count_13_5 := by decide +kernel
noncomputable def Count_13_6 : Nat := prob_row% 13 6
theorem count_13_6 : rowFast cache64 13 6=Count_13_6 := by decide +kernel
noncomputable def Count_13_7 : Nat := prob_row% 13 7
theorem count_13_7 : rowFast cache64 13 7=Count_13_7 := by decide +kernel
noncomputable def Count_13_8 : Nat := prob_row% 13 8
theorem count_13_8 : rowFast cache64 13 8=Count_13_8 := by decide +kernel
noncomputable def Count_13_9 : Nat := prob_row% 13 9
theorem count_13_9 : rowFast cache64 13 9=Count_13_9 := by decide +kernel
noncomputable def Count_13_10 : Nat := prob_row% 13 10
theorem count_13_10 : rowFast cache64 13 10=Count_13_10 := by decide +kernel
noncomputable def Count_13_11 : Nat := prob_row% 13 11
theorem count_13_11 : rowFast cache64 13 11=Count_13_11 := by decide +kernel
noncomputable def Count_13_12 : Nat := prob_row% 13 12
theorem count_13_12 : rowFast cache64 13 12=Count_13_12 := by decide +kernel
noncomputable def Count_13_13 : Nat := prob_row% 13 13
theorem count_13_13 : rowFast cache64 13 13=Count_13_13 := by decide +kernel
noncomputable def countRow_13 (t : Nat) : Nat :=
  match t with
  | 0 => Count_13_0
  | 1 => Count_13_1
  | 2 => Count_13_2
  | 3 => Count_13_3
  | 4 => Count_13_4
  | 5 => Count_13_5
  | 6 => Count_13_6
  | 7 => Count_13_7
  | 8 => Count_13_8
  | 9 => Count_13_9
  | 10 => Count_13_10
  | 11 => Count_13_11
  | 12 => Count_13_12
  | 13 => Count_13_13
  | _ => 0
theorem countRow_13_checked (t : Nat) (ht : t≤13) : row 13 t=countRow_13 t := by
  rw [row_eq 13 t (by omega) ht]
  interval_cases t
  · exact count_13_0
  · exact count_13_1
  · exact count_13_2
  · exact count_13_3
  · exact count_13_4
  · exact count_13_5
  · exact count_13_6
  · exact count_13_7
  · exact count_13_8
  · exact count_13_9
  · exact count_13_10
  · exact count_13_11
  · exact count_13_12
  · exact count_13_13
noncomputable def Pair_13 : Nat := prob_pair% 13
theorem pair_13_checked : pairPacked 13=Pair_13 :=
  (pair_of_rows 13 countRow_13 countRow_13_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
