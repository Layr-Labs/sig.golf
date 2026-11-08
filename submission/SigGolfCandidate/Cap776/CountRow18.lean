import SigGolfCandidate.Cap776.CountRow17
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
noncomputable def Count_18_0 : Nat := prob_row% 18 0
theorem count_18_0 : rowFast cache64 18 0=Count_18_0 := by decide +kernel
noncomputable def Count_18_1 : Nat := prob_row% 18 1
theorem count_18_1 : rowFast cache64 18 1=Count_18_1 := by decide +kernel
noncomputable def Count_18_2 : Nat := prob_row% 18 2
theorem count_18_2 : rowFast cache64 18 2=Count_18_2 := by decide +kernel
noncomputable def Count_18_3 : Nat := prob_row% 18 3
theorem count_18_3 : rowFast cache64 18 3=Count_18_3 := by decide +kernel
noncomputable def Count_18_4 : Nat := prob_row% 18 4
theorem count_18_4 : rowFast cache64 18 4=Count_18_4 := by decide +kernel
noncomputable def Count_18_5 : Nat := prob_row% 18 5
theorem count_18_5 : rowFast cache64 18 5=Count_18_5 := by decide +kernel
noncomputable def Count_18_6 : Nat := prob_row% 18 6
theorem count_18_6 : rowFast cache64 18 6=Count_18_6 := by decide +kernel
noncomputable def Count_18_7 : Nat := prob_row% 18 7
theorem count_18_7 : rowFast cache64 18 7=Count_18_7 := by decide +kernel
noncomputable def Count_18_8 : Nat := prob_row% 18 8
theorem count_18_8 : rowFast cache64 18 8=Count_18_8 := by decide +kernel
noncomputable def Count_18_9 : Nat := prob_row% 18 9
theorem count_18_9 : rowFast cache64 18 9=Count_18_9 := by decide +kernel
noncomputable def Count_18_10 : Nat := prob_row% 18 10
theorem count_18_10 : rowFast cache64 18 10=Count_18_10 := by decide +kernel
noncomputable def Count_18_11 : Nat := prob_row% 18 11
theorem count_18_11 : rowFast cache64 18 11=Count_18_11 := by decide +kernel
noncomputable def Count_18_12 : Nat := prob_row% 18 12
theorem count_18_12 : rowFast cache64 18 12=Count_18_12 := by decide +kernel
noncomputable def Count_18_13 : Nat := prob_row% 18 13
theorem count_18_13 : rowFast cache64 18 13=Count_18_13 := by decide +kernel
noncomputable def Count_18_14 : Nat := prob_row% 18 14
theorem count_18_14 : rowFast cache64 18 14=Count_18_14 := by decide +kernel
noncomputable def Count_18_15 : Nat := prob_row% 18 15
theorem count_18_15 : rowFast cache64 18 15=Count_18_15 := by decide +kernel
noncomputable def Count_18_16 : Nat := prob_row% 18 16
theorem count_18_16 : rowFast cache64 18 16=Count_18_16 := by decide +kernel
noncomputable def Count_18_17 : Nat := prob_row% 18 17
theorem count_18_17 : rowFast cache64 18 17=Count_18_17 := by decide +kernel
noncomputable def Count_18_18 : Nat := prob_row% 18 18
theorem count_18_18 : rowFast cache64 18 18=Count_18_18 := by decide +kernel
noncomputable def countRow_18 (t : Nat) : Nat :=
  match t with
  | 0 => Count_18_0
  | 1 => Count_18_1
  | 2 => Count_18_2
  | 3 => Count_18_3
  | 4 => Count_18_4
  | 5 => Count_18_5
  | 6 => Count_18_6
  | 7 => Count_18_7
  | 8 => Count_18_8
  | 9 => Count_18_9
  | 10 => Count_18_10
  | 11 => Count_18_11
  | 12 => Count_18_12
  | 13 => Count_18_13
  | 14 => Count_18_14
  | 15 => Count_18_15
  | 16 => Count_18_16
  | 17 => Count_18_17
  | 18 => Count_18_18
  | _ => 0
theorem countRow_18_checked (t : Nat) (ht : t≤18) : row 18 t=countRow_18 t := by
  rw [row_eq 18 t (by omega) ht]
  interval_cases t
  · exact count_18_0
  · exact count_18_1
  · exact count_18_2
  · exact count_18_3
  · exact count_18_4
  · exact count_18_5
  · exact count_18_6
  · exact count_18_7
  · exact count_18_8
  · exact count_18_9
  · exact count_18_10
  · exact count_18_11
  · exact count_18_12
  · exact count_18_13
  · exact count_18_14
  · exact count_18_15
  · exact count_18_16
  · exact count_18_17
  · exact count_18_18
noncomputable def Pair_18 : Nat := prob_pair% 18
theorem pair_18_checked : pairPacked 18=Pair_18 :=
  (pair_of_rows 18 countRow_18 countRow_18_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
