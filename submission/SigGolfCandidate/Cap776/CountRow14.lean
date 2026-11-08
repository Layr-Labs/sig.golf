import SigGolfCandidate.Cap776.CountRow13
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
noncomputable def Count_14_0 : Nat := prob_row% 14 0
theorem count_14_0 : rowFast cache64 14 0=Count_14_0 := by decide +kernel
noncomputable def Count_14_1 : Nat := prob_row% 14 1
theorem count_14_1 : rowFast cache64 14 1=Count_14_1 := by decide +kernel
noncomputable def Count_14_2 : Nat := prob_row% 14 2
theorem count_14_2 : rowFast cache64 14 2=Count_14_2 := by decide +kernel
noncomputable def Count_14_3 : Nat := prob_row% 14 3
theorem count_14_3 : rowFast cache64 14 3=Count_14_3 := by decide +kernel
noncomputable def Count_14_4 : Nat := prob_row% 14 4
theorem count_14_4 : rowFast cache64 14 4=Count_14_4 := by decide +kernel
noncomputable def Count_14_5 : Nat := prob_row% 14 5
theorem count_14_5 : rowFast cache64 14 5=Count_14_5 := by decide +kernel
noncomputable def Count_14_6 : Nat := prob_row% 14 6
theorem count_14_6 : rowFast cache64 14 6=Count_14_6 := by decide +kernel
noncomputable def Count_14_7 : Nat := prob_row% 14 7
theorem count_14_7 : rowFast cache64 14 7=Count_14_7 := by decide +kernel
noncomputable def Count_14_8 : Nat := prob_row% 14 8
theorem count_14_8 : rowFast cache64 14 8=Count_14_8 := by decide +kernel
noncomputable def Count_14_9 : Nat := prob_row% 14 9
theorem count_14_9 : rowFast cache64 14 9=Count_14_9 := by decide +kernel
noncomputable def Count_14_10 : Nat := prob_row% 14 10
theorem count_14_10 : rowFast cache64 14 10=Count_14_10 := by decide +kernel
noncomputable def Count_14_11 : Nat := prob_row% 14 11
theorem count_14_11 : rowFast cache64 14 11=Count_14_11 := by decide +kernel
noncomputable def Count_14_12 : Nat := prob_row% 14 12
theorem count_14_12 : rowFast cache64 14 12=Count_14_12 := by decide +kernel
noncomputable def Count_14_13 : Nat := prob_row% 14 13
theorem count_14_13 : rowFast cache64 14 13=Count_14_13 := by decide +kernel
noncomputable def Count_14_14 : Nat := prob_row% 14 14
theorem count_14_14 : rowFast cache64 14 14=Count_14_14 := by decide +kernel
noncomputable def countRow_14 (t : Nat) : Nat :=
  match t with
  | 0 => Count_14_0
  | 1 => Count_14_1
  | 2 => Count_14_2
  | 3 => Count_14_3
  | 4 => Count_14_4
  | 5 => Count_14_5
  | 6 => Count_14_6
  | 7 => Count_14_7
  | 8 => Count_14_8
  | 9 => Count_14_9
  | 10 => Count_14_10
  | 11 => Count_14_11
  | 12 => Count_14_12
  | 13 => Count_14_13
  | 14 => Count_14_14
  | _ => 0
theorem countRow_14_checked (t : Nat) (ht : t≤14) : row 14 t=countRow_14 t := by
  rw [row_eq 14 t (by omega) ht]
  interval_cases t
  · exact count_14_0
  · exact count_14_1
  · exact count_14_2
  · exact count_14_3
  · exact count_14_4
  · exact count_14_5
  · exact count_14_6
  · exact count_14_7
  · exact count_14_8
  · exact count_14_9
  · exact count_14_10
  · exact count_14_11
  · exact count_14_12
  · exact count_14_13
  · exact count_14_14
noncomputable def Pair_14 : Nat := prob_pair% 14
theorem pair_14_checked : pairPacked 14=Pair_14 :=
  (pair_of_rows 14 countRow_14 countRow_14_checked).trans (by decide +kernel)

end SigGolfResearch.ProbabilityCache
