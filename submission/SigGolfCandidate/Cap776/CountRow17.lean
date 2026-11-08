import SigGolfCandidate.Cap776.CountRow16
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
noncomputable def Count_17_0 : Nat := prob_row% 17 0
theorem count_17_0 : rowFast cache64 17 0=Count_17_0 := by decide +kernel
noncomputable def Count_17_1 : Nat := prob_row% 17 1
theorem count_17_1 : rowFast cache64 17 1=Count_17_1 := by decide +kernel
noncomputable def Count_17_2 : Nat := prob_row% 17 2
theorem count_17_2 : rowFast cache64 17 2=Count_17_2 := by decide +kernel
noncomputable def Count_17_3 : Nat := prob_row% 17 3
theorem count_17_3 : rowFast cache64 17 3=Count_17_3 := by decide +kernel
noncomputable def Count_17_4 : Nat := prob_row% 17 4
theorem count_17_4 : rowFast cache64 17 4=Count_17_4 := by decide +kernel
noncomputable def Count_17_5 : Nat := prob_row% 17 5
theorem count_17_5 : rowFast cache64 17 5=Count_17_5 := by decide +kernel
noncomputable def Count_17_6 : Nat := prob_row% 17 6
theorem count_17_6 : rowFast cache64 17 6=Count_17_6 := by decide +kernel
noncomputable def Count_17_7 : Nat := prob_row% 17 7
theorem count_17_7 : rowFast cache64 17 7=Count_17_7 := by decide +kernel
noncomputable def Count_17_8 : Nat := prob_row% 17 8
theorem count_17_8 : rowFast cache64 17 8=Count_17_8 := by decide +kernel
noncomputable def Count_17_9 : Nat := prob_row% 17 9
theorem count_17_9 : rowFast cache64 17 9=Count_17_9 := by decide +kernel
noncomputable def Count_17_10 : Nat := prob_row% 17 10
theorem count_17_10 : rowFast cache64 17 10=Count_17_10 := by decide +kernel
noncomputable def Count_17_11 : Nat := prob_row% 17 11
theorem count_17_11 : rowFast cache64 17 11=Count_17_11 := by decide +kernel
noncomputable def Count_17_12 : Nat := prob_row% 17 12
theorem count_17_12 : rowFast cache64 17 12=Count_17_12 := by decide +kernel
noncomputable def Count_17_13 : Nat := prob_row% 17 13
theorem count_17_13 : rowFast cache64 17 13=Count_17_13 := by decide +kernel
noncomputable def Count_17_14 : Nat := prob_row% 17 14
theorem count_17_14 : rowFast cache64 17 14=Count_17_14 := by decide +kernel
noncomputable def Count_17_15 : Nat := prob_row% 17 15
theorem count_17_15 : rowFast cache64 17 15=Count_17_15 := by decide +kernel
noncomputable def Count_17_16 : Nat := prob_row% 17 16
theorem count_17_16 : rowFast cache64 17 16=Count_17_16 := by decide +kernel
noncomputable def Count_17_17 : Nat := prob_row% 17 17
theorem count_17_17 : rowFast cache64 17 17=Count_17_17 := by decide +kernel
noncomputable def countRow_17 (t : Nat) : Nat :=
  match t with
  | 0 => Count_17_0
  | 1 => Count_17_1
  | 2 => Count_17_2
  | 3 => Count_17_3
  | 4 => Count_17_4
  | 5 => Count_17_5
  | 6 => Count_17_6
  | 7 => Count_17_7
  | 8 => Count_17_8
  | 9 => Count_17_9
  | 10 => Count_17_10
  | 11 => Count_17_11
  | 12 => Count_17_12
  | 13 => Count_17_13
  | 14 => Count_17_14
  | 15 => Count_17_15
  | 16 => Count_17_16
  | 17 => Count_17_17
  | _ => 0
theorem countRow_17_checked (t : Nat) (ht : t≤17) : row 17 t=countRow_17 t := by
  rw [row_eq 17 t (by omega) ht]
  interval_cases t
  · exact count_17_0
  · exact count_17_1
  · exact count_17_2
  · exact count_17_3
  · exact count_17_4
  · exact count_17_5
  · exact count_17_6
  · exact count_17_7
  · exact count_17_8
  · exact count_17_9
  · exact count_17_10
  · exact count_17_11
  · exact count_17_12
  · exact count_17_13
  · exact count_17_14
  · exact count_17_15
  · exact count_17_16
  · exact count_17_17
noncomputable def Pair_17 : Nat := prob_pair% 17
theorem pair_17_checked : pairPacked 17=Pair_17 :=
  (pair_of_rows 17 countRow_17 countRow_17_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
