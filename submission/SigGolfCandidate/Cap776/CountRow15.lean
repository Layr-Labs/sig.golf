import SigGolfCandidate.Cap776.CountRow14
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
noncomputable def Count_15_0 : Nat := prob_row% 15 0
theorem count_15_0 : rowFast cache64 15 0=Count_15_0 := by decide +kernel
noncomputable def Count_15_1 : Nat := prob_row% 15 1
theorem count_15_1 : rowFast cache64 15 1=Count_15_1 := by decide +kernel
noncomputable def Count_15_2 : Nat := prob_row% 15 2
theorem count_15_2 : rowFast cache64 15 2=Count_15_2 := by decide +kernel
noncomputable def Count_15_3 : Nat := prob_row% 15 3
theorem count_15_3 : rowFast cache64 15 3=Count_15_3 := by decide +kernel
noncomputable def Count_15_4 : Nat := prob_row% 15 4
theorem count_15_4 : rowFast cache64 15 4=Count_15_4 := by decide +kernel
noncomputable def Count_15_5 : Nat := prob_row% 15 5
theorem count_15_5 : rowFast cache64 15 5=Count_15_5 := by decide +kernel
noncomputable def Count_15_6 : Nat := prob_row% 15 6
theorem count_15_6 : rowFast cache64 15 6=Count_15_6 := by decide +kernel
noncomputable def Count_15_7 : Nat := prob_row% 15 7
theorem count_15_7 : rowFast cache64 15 7=Count_15_7 := by decide +kernel
noncomputable def Count_15_8 : Nat := prob_row% 15 8
theorem count_15_8 : rowFast cache64 15 8=Count_15_8 := by decide +kernel
noncomputable def Count_15_9 : Nat := prob_row% 15 9
theorem count_15_9 : rowFast cache64 15 9=Count_15_9 := by decide +kernel
noncomputable def Count_15_10 : Nat := prob_row% 15 10
theorem count_15_10 : rowFast cache64 15 10=Count_15_10 := by decide +kernel
noncomputable def Count_15_11 : Nat := prob_row% 15 11
theorem count_15_11 : rowFast cache64 15 11=Count_15_11 := by decide +kernel
noncomputable def Count_15_12 : Nat := prob_row% 15 12
theorem count_15_12 : rowFast cache64 15 12=Count_15_12 := by decide +kernel
noncomputable def Count_15_13 : Nat := prob_row% 15 13
theorem count_15_13 : rowFast cache64 15 13=Count_15_13 := by decide +kernel
noncomputable def Count_15_14 : Nat := prob_row% 15 14
theorem count_15_14 : rowFast cache64 15 14=Count_15_14 := by decide +kernel
noncomputable def Count_15_15 : Nat := prob_row% 15 15
theorem count_15_15 : rowFast cache64 15 15=Count_15_15 := by decide +kernel
noncomputable def countRow_15 (t : Nat) : Nat :=
  match t with
  | 0 => Count_15_0
  | 1 => Count_15_1
  | 2 => Count_15_2
  | 3 => Count_15_3
  | 4 => Count_15_4
  | 5 => Count_15_5
  | 6 => Count_15_6
  | 7 => Count_15_7
  | 8 => Count_15_8
  | 9 => Count_15_9
  | 10 => Count_15_10
  | 11 => Count_15_11
  | 12 => Count_15_12
  | 13 => Count_15_13
  | 14 => Count_15_14
  | 15 => Count_15_15
  | _ => 0
theorem countRow_15_checked (t : Nat) (ht : t≤15) : row 15 t=countRow_15 t := by
  rw [row_eq 15 t (by omega) ht]
  interval_cases t
  · exact count_15_0
  · exact count_15_1
  · exact count_15_2
  · exact count_15_3
  · exact count_15_4
  · exact count_15_5
  · exact count_15_6
  · exact count_15_7
  · exact count_15_8
  · exact count_15_9
  · exact count_15_10
  · exact count_15_11
  · exact count_15_12
  · exact count_15_13
  · exact count_15_14
  · exact count_15_15
noncomputable def Pair_15 : Nat := prob_pair% 15
theorem pair_15_checked : pairPacked 15=Pair_15 :=
  (pair_of_rows 15 countRow_15 countRow_15_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
